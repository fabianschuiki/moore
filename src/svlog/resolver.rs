// Copyright (c) 2016-2020 Fabian Schuiki

//! Name resolution.
//!
//! This module implements the infrastructure to describe scopes and resolve
//! names in them.

use crate::{
    ast_map::AstNode,
    common::{SessionContext, Verbosity},
    crate_prelude::*,
    hir::HirNode,
    ty::TypeKind,
    ParamEnv,
};
use std::{
    collections::{BTreeSet, HashMap},
    sync::Arc,
};

/// One local scope.
///
/// A rib represents a any kind of scope. Ribs form a tree structure along their
/// parents that may be traversed from the bottom to the top to perform name
/// resolution, or top to bottom to lookup hierarchical names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rib {
    /// The node this rib is associated with.
    ///
    /// When querying the compiler for a node's rib, what you get in return is
    /// not necessarily the rib of that node. If the node does not generate a
    /// new rib, you get back the rib of a parent node.
    pub node: NodeId,
    /// The parent rib.
    ///
    /// Note that this does not necessarily correspond to the parent node, but
    /// may skip nodes that do not contain a rib.
    pub parent: Option<NodeId>,
    /// The data associated with the rib.
    pub kind: RibKind,
}

/// A local scope kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RibKind {
    /// A normal declaration.
    Normal(Spanned<Name>, NodeId),
    /// A module.
    Module(HashMap<Name, NodeId>),
    /// An enum type declaration.
    Enum(HashMap<Name, NodeId>),
    /// An imported rib.
    Import(Box<Rib>),
}

impl Rib {
    /// Look up a name.
    pub fn get(&self, name: Name) -> Option<NodeId> {
        self.kind.get(name)
    }

    /// Resolve import ribs to the imported rib.
    pub fn resolve_imports(&self) -> &Self {
        match &self.kind {
            RibKind::Import(rib) => rib.as_ref(),
            _ => self,
        }
    }
}

impl RibKind {
    /// Look up a name.
    pub fn get(&self, name: Name) -> Option<NodeId> {
        match *self {
            RibKind::Normal(n, id) if n.value == name => Some(id),
            RibKind::Module(ref defs) | RibKind::Enum(ref defs) => defs.get(&name).cloned(),
            _ => None,
        }
    }
}

/// Determine the local rib that applies to a node.
///
/// This will return either the rib the node itself generates, or the next rib
/// up the hierarchy.
pub(crate) fn local_rib<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<&'gcx Rib> {
    let ast = cx.ast_of(node_id)?;
    trace!("local_rib for {} ({:?})", ast.desc_full(), node_id);
    let mut parent = None;
    let mut kind = match ast {
        AstNode::TypeParam(_, decl) => Some(RibKind::Normal(
            Spanned::new(decl.name.name, decl.name.span),
            node_id,
        )),
        AstNode::ValueParam(_, decl) => Some(RibKind::Normal(
            Spanned::new(decl.name.name, decl.name.span),
            node_id,
        )),
        AstNode::Module(_) => Some(RibKind::Module(HashMap::new())),
        AstNode::VarDecl(decl, _, _) | AstNode::NetDecl(decl, _, _) => Some(RibKind::Normal(
            Spanned::new(decl.name, decl.name_span),
            node_id,
        )),
        AstNode::GenvarDecl(decl) => Some(RibKind::Normal(
            Spanned::new(decl.name, decl.name_span),
            node_id,
        )),
        AstNode::Stmt(stmt) => match stmt.data {
            ast::VarDeclStmt(_) => {
                let hir = match cx.hir_of(node_id)? {
                    HirNode::Stmt(x) => x,
                    _ => unreachable!(),
                };
                match hir.kind {
                    hir::StmtKind::InlineGroup { rib, .. } => return cx.local_rib(rib),
                    _ => None,
                }
            }
            _ => None,
        },
        AstNode::Package(_) => Some(RibKind::Module(HashMap::new())),
        AstNode::Type(_) => {
            let hir = match cx.hir_of(node_id)? {
                HirNode::Type(x) => x,
                _ => unreachable!(),
            };
            local_rib_kind_for_type(cx, &hir.kind)
        }
        AstNode::Import(import) => {
            let pkg_id = match cx.gcx().find_package(import.pkg.value) {
                Some(id) => id,
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!("`{}` not found", import.pkg.value))
                            .span(import.pkg.span),
                    );
                    return Err(());
                }
            };
            if let Some(name) = import.name {
                trace!(
                    "Importing single `{}` from `{}`: {}",
                    name,
                    import.pkg,
                    cx.ast_of(pkg_id)?.desc_full()
                );
                let resolved = cx.resolve_downwards_or_error(name, pkg_id)?;
                let rib = cx.local_rib(resolved)?;
                Some(RibKind::Import(Box::new(rib.clone())))
            } else {
                let rib = cx.hierarchical_rib(pkg_id)?;
                trace!("Importing entire `{}`: {:#?}", import.pkg, rib);
                Some(RibKind::Import(Box::new(rib.clone())))
            }
        }
        AstNode::SubroutineDecl(decl) => Some(RibKind::Normal(
            Spanned::new(decl.prototype.name.name, decl.prototype.name.span),
            node_id,
        )),
        _ => None,
    };
    if kind.is_none() {
        let hir = cx.hir_of(node_id)?;
        kind = match hir {
            HirNode::Typedef(def) => {
                parent = Some(def.ty);
                Some(RibKind::Normal(
                    Spanned::new(def.name.value, def.name.span),
                    node_id,
                ))
            }
            HirNode::IntPort(port) => Some(RibKind::Normal(port.name, node_id)),
            _ => None,
        };
    }
    let kind = match kind {
        Some(kind) => kind,
        None => {
            return cx.local_rib(
                cx.parent_node_id(node_id)
                    .expect("root node must produce a rib"),
            );
        }
    };
    let rib = Rib {
        node: node_id,
        parent: match parent.or_else(|| cx.parent_node_id(node_id)) {
            Some(parent_id) => Some(cx.local_rib(parent_id)?.node),
            None => None,
        },
        kind: kind,
    };
    if cx.sess().has_verbosity(Verbosity::NAMES) {
        let mut d = DiagBuilder2::note(format!(
            "created local rib for {}",
            cx.ast_of(node_id)?.desc_full()
        ))
        .span(cx.span(node_id))
        .add_note(format!("{:?}", rib.kind));
        if let Some(parent) = rib.parent {
            d = d
                .add_note("Parent is here:".to_string())
                .span(cx.span(parent));
        }
        cx.emit(d);
    }
    Ok(cx.arena().alloc_rib(rib))
}

fn local_rib_kind_for_type<'gcx>(cx: &impl Context<'gcx>, kind: &hir::TypeKind) -> Option<RibKind> {
    trace!("creating local rib for type {:#?}", kind);
    match kind {
        hir::TypeKind::PackedArray(inner, ..) => local_rib_kind_for_type(cx, inner.as_ref()),
        hir::TypeKind::Enum(ref variants, _) => Some(RibKind::Enum(
            variants
                .iter()
                .map(|(name, id)| (name.value, *id))
                .collect(),
        )),
        _ => None,
    }
}

/// Determine the hierarchical rib of a node.
///
/// This will return a rib containing the hierarchical names exposed by a node.
pub(crate) fn hierarchical_rib<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
) -> Result<&'gcx Rib> {
    let hir = cx.hir_of(node_id)?;
    let mut names = HashMap::new();
    let mut rib_id = match hir {
        HirNode::Package(pkg) => Some(pkg.last_rib),
        HirNode::Module(module) => Some(module.last_rib),
        _ => panic!("{} has no hierarchical rib", hir.desc_full()),
    };
    while let Some(id) = rib_id {
        let rib = cx.local_rib(id)?;
        match rib.kind {
            RibKind::Normal(name, def) => {
                names.insert(name.value, def);
            }
            RibKind::Module(ref defs) => names.extend(defs),
            RibKind::Enum(ref defs) => names.extend(defs),
            RibKind::Import(_) => (), // imports are never visible
        }
        rib_id = rib.parent;
        if rib_id == Some(node_id) {
            rib_id = None;
        }
    }
    let rib = Rib {
        node: node_id,
        parent: None,
        kind: RibKind::Module(names),
    };
    Ok(cx.arena().alloc_rib(rib))
}

/// Resolve a name upwards through the ribs.
///
/// This is equivalent to performing regular scoped namespace lookup.
pub(crate) fn resolve_upwards<'gcx>(
    cx: &impl Context<'gcx>,
    name: Name,
    start_at: NodeId,
) -> Result<Option<NodeId>> {
    if cx.sess().has_verbosity(Verbosity::NAMES) {
        cx.emit(DiagBuilder2::note(format!("resolving `{}`", name)).span(cx.span(start_at)));
    }
    let mut next_id = Some(start_at);
    while let Some(rib_id) = next_id {
        if cx.sess().has_verbosity(Verbosity::NAMES) {
            cx.emit(DiagBuilder2::note(format!("resolving `{}` here", name)).span(cx.span(rib_id)));
        }
        let rib = cx.local_rib(rib_id)?;
        if let Some(resolved) = resolve_in_rib(cx, name, rib)? {
            return Ok(Some(resolved));
        }
        next_id = rib.parent;
    }
    for import in cx.gcx().imports() {
        if let n @ Some(_) = resolve_in_rib(cx, name, cx.local_rib(import)?)? {
            return Ok(n);
        }
    }
    if let m @ Some(_) = cx.gcx().find_module(name) {
        return Ok(m);
    }
    if let p @ Some(_) = cx.gcx().find_package(name) {
        return Ok(p);
    }
    Ok(None)
}

fn resolve_in_rib<'gcx>(cx: &impl Context<'gcx>, name: Name, rib: &Rib) -> Result<Option<NodeId>> {
    let rib_resolved = rib.resolve_imports();
    if let Some(id) = rib_resolved.get(name) {
        return Ok(Some(id));
    }
    if let RibKind::Module(..) = rib_resolved.kind {
        let rib = cx.hierarchical_rib(rib_resolved.node)?;
        if let Some(id) = rib.get(name) {
            return Ok(Some(id));
        }
    }
    Ok(None)
}

/// Resolve a name downwards.
///
/// This is equivalent to performing a hierarchical name lookup.
pub(crate) fn resolve_downwards<'gcx>(
    cx: &impl Context<'gcx>,
    name: Name,
    start_at: NodeId,
) -> Result<Option<NodeId>> {
    let rib = cx.hierarchical_rib(start_at)?;
    Ok(match rib.get(name) {
        Some(x) => Some(x),
        None => {
            debug!("name `{}` not found in {:#?}", name, rib);
            None
        }
    })
}

/// Resolve a node to its target.
pub(crate) fn resolve_node<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<NodeId> {
    let hir = cx.hir_of(node_id)?;
    match hir {
        HirNode::Expr(expr) => match expr.kind {
            hir::ExprKind::Ident(ident) => return cx.resolve_upwards_or_error(ident, node_id),
            hir::ExprKind::Scope(scope_id, name) => {
                let within = cx.resolve_node(scope_id, env)?;
                return cx.resolve_downwards_or_error(name, within);
            }
            _ => (),
        },
        HirNode::Type(ty) => match ty.kind {
            hir::TypeKind::Named(name) => return cx.resolve_upwards_or_error(name, node_id),
            hir::TypeKind::Scope(scope_id, name) => {
                let within = cx.resolve_node(scope_id, env)?;
                return cx.resolve_downwards_or_error(name, within);
            }
            _ => (),
        },
        HirNode::IntPort(port) if port.data.is_none() => {
            return cx.resolve_downwards_or_error(port.name, port.module);
        }
        _ => (),
    }
    error!("{:#?}", hir);
    cx.emit(DiagBuilder2::bug("cannot resolve node").span(hir.human_span()));
    Err(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDef {
    pub packed: bool,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub name: Spanned<Name>,
    pub ty: NodeId,
}

/// Obtain the details of a struct definition.
pub(crate) fn struct_def<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<Arc<StructDef>> {
    let hir = cx.hir_of(node_id)?;
    let struct_fields = match hir {
        HirNode::Type(hir::Type {
            kind: hir::TypeKind::Struct(ref fields),
            ..
        }) => fields,
        _ => {
            cx.emit(
                DiagBuilder2::error(format!("{} is not a struct", hir.desc_full()))
                    .span(hir.human_span()),
            );
            return Err(());
        }
    };
    let fields = struct_fields
        .iter()
        .flat_map(|&id| match cx.hir_of(id) {
            Ok(HirNode::VarDecl(vd)) => Some(StructField {
                name: vd.name,
                ty: vd.ty,
            }),
            _ => None,
        })
        .collect();
    Ok(Arc::new(StructDef {
        packed: true,
        fields,
    }))
}

/// Resolve the field name in a field access expression.
pub(crate) fn resolve_field_access<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<(NodeId, usize, NodeId)> {
    let hir = match cx.hir_of(node_id)? {
        HirNode::Expr(x) => x,
        _ => unreachable!(),
    };
    let (target_id, name) = match hir.kind {
        hir::ExprKind::Field(target_id, name) => (target_id, name),
        _ => unreachable!(),
    };
    let ty = cx.type_of(target_id, env)?;
    let struct_def = match ty.resolve_name() {
        TypeKind::Error => return Err(()),
        &TypeKind::Struct(id) => id,
        _ => {
            let target_hir = cx.hir_of(target_id)?;
            let mut d = DiagBuilder2::error(format!(
                "{} has no fields; type `{}` is not a struct",
                target_hir.desc_full(),
                ty
            ))
            .span(hir.human_span());
            if let TypeKind::Named(_, def_id, inner_ty) = *ty {
                d = d
                    .add_note(format!("Type `{}` is defined as `{}` here:", ty, inner_ty))
                    .span(cx.span(def_id));
            }
            cx.emit(d);
            error!("Cannot resolve field access {:?}", hir);
            error!("Target is {:?}", target_hir);
            error!("Type is {:?}", ty);
            return Err(());
        }
    };
    let struct_fields = match cx.hir_of(struct_def)? {
        HirNode::Type(hir::Type {
            kind: hir::TypeKind::Struct(ref fields),
            ..
        }) => fields,
        _ => unreachable!(),
    };
    let index = struct_fields.iter().position(|&id| match cx.hir_of(id) {
        Ok(HirNode::VarDecl(vd)) => vd.name.value == name.value,
        _ => false,
    });
    let index = match index {
        Some(x) => x,
        None => {
            let hir = cx.hir_of(target_id)?;
            cx.emit(
                DiagBuilder2::error(format!("{} has no field `{}`", hir.desc_full(), name))
                    .span(name.span())
                    .add_note(format!("{} is a struct defined here:", hir.desc_full()))
                    .span(cx.span(struct_def)),
            );
            return Err(());
        }
    };
    Ok((struct_def, index, struct_fields[index]))
}

/// Resolve the fields in an assignment pattern.
#[allow(dead_code)]
pub(crate) fn resolve_pattern<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Vec<(usize, NodeId)>> {
    let hir = match cx.hir_of(node_id)? {
        HirNode::Expr(x) => x,
        _ => unreachable!(),
    };
    let ty = cx.type_of(node_id, env)?;
    match ty {
        &TypeKind::Named(_, _, &TypeKind::Struct(struct_id)) | &TypeKind::Struct(struct_id) => {
            trace!("struct pattern: defined at {:?}", struct_id);
            let struct_fields = match cx.hir_of(struct_id)? {
                HirNode::Type(hir::Type {
                    kind: hir::TypeKind::Struct(ref fields),
                    ..
                }) => fields,
                _ => unreachable!(),
            };
            let struct_fields: Vec<_> = struct_fields
                .iter()
                .filter_map(|&id| match cx.hir_of(id) {
                    Ok(HirNode::VarDecl(vd)) => Some(vd),
                    _ => None,
                })
                .collect();
            trace!("matching against fields: {:#?}", struct_fields);
            let mut assigned = vec![];
            let mut missing: BTreeSet<usize> = (0..struct_fields.len()).collect();
            match hir.kind {
                hir::ExprKind::PositionalPattern(ref fields) => {
                    for (i, &expr_id) in fields.iter().enumerate() {
                        if i >= struct_fields.len() {
                            cx.emit(
                                DiagBuilder2::error(format!(
                                    "`{}` only has {} fields",
                                    ty,
                                    struct_fields.len()
                                ))
                                .span(cx.ast_of(expr_id)?.span()),
                            );
                            continue;
                        }
                        missing.remove(&i);
                        assigned.push((i, expr_id));
                    }
                }
                hir::ExprKind::NamedPattern(ref fields) => {
                    let mut default = None;
                    for &(mapping, expr_id) in fields {
                        match mapping {
                            hir::PatternMapping::Member(member_id) => {
                                let ast = cx.ast_of(member_id)?;
                                let name = match ast {
                                    AstNode::Expr(&ast::Expr {
                                        data: ast::IdentExpr(ident),
                                        ..
                                    }) => Spanned::new(ident.name, ident.span),
                                    _ => {
                                        cx.emit(
                                            DiagBuilder2::error(format!(
                                                "`{}` is not a valid field name",
                                                ast.span().extract()
                                            ))
                                            .span(ast.span()),
                                        );
                                        continue;
                                    }
                                };
                                let index = struct_fields
                                    .iter()
                                    .position(|&vd| vd.name.value == name.value);
                                let index = match index {
                                    Some(index) => index,
                                    None => {
                                        cx.emit(
                                            DiagBuilder2::error(format!(
                                                "`{}` has no field `{}`",
                                                ty, name
                                            ))
                                            .span(name.span()),
                                        );
                                        continue;
                                    }
                                };
                                if !missing.contains(&index) {
                                    cx.emit(
                                        DiagBuilder2::error(format!(
                                            "`{}` assigned multiple times",
                                            name
                                        ))
                                        .span(name.span()),
                                    );
                                    continue;
                                }
                                missing.remove(&index);
                                assigned.push((index, expr_id));
                            }
                            hir::PatternMapping::Default if default.is_none() => {
                                default = Some(expr_id);
                            }
                            hir::PatternMapping::Default => {
                                cx.emit(
                                    DiagBuilder2::error("multiple default assignments in pattern")
                                        .span(hir.span()),
                                );
                                continue;
                            }
                            hir::PatternMapping::Type(type_id) => {
                                cx.emit(
                                    DiagBuilder2::bug("type pattern keys not implemented")
                                        .span(cx.ast_of(type_id)?.span()),
                                );
                                continue;
                            }
                        }
                    }
                    if let Some(expr_id) = default {
                        for i in std::mem::replace(&mut missing, BTreeSet::new()) {
                            assigned.push((i, expr_id))
                        }
                    }
                }
                _ => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "`{}` cannot be accessed by a {}",
                            ty,
                            hir.desc_full()
                        ))
                        .span(hir.span),
                    );
                    return Err(());
                }
            }
            if !missing.is_empty() {
                let names: String = missing
                    .into_iter()
                    .map(|i| format!("`{}`", struct_fields[i].name.value))
                    .collect::<Vec<_>>()
                    .join(", ");
                cx.emit(
                    DiagBuilder2::error(format!("fields {} not assigned by pattern", names,))
                        .span(hir.span),
                );
            }
            return Ok(assigned);
        }
        &TypeKind::Named(_, _, &TypeKind::PackedArray(length, elem_ty))
        | &TypeKind::PackedArray(length, elem_ty) => {
            trace!("array pattern: {} elements of type {:?}", length, elem_ty);
            cx.emit(
                DiagBuilder2::error(format!(
                    "`{}` cannot be accessed by a {}",
                    ty,
                    hir.desc_full()
                ))
                .span(hir.span),
            );
            return Err(());
        }
        _ => {
            cx.emit(
                DiagBuilder2::error(format!("type `{}` cannot be used with a pattern", ty))
                    .span(hir.span),
            );
            return Err(());
        }
    }
}

/// Determine the scope generated by a node.
pub fn generated_scope_query<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<()> {
    let ast = cx.ast_of(node_id)?;
    match ast {
        AstNode::Module(node) => generated_scope(cx, Ref::from(node)),
        AstNode::Package(node) => generated_scope(cx, Ref::from(node)),
        _ => bug_span!(ast.span(), cx, "node does not generate a scope"),
    }
    Ok(())
}

/// Marker trait for AST nodes that generate a scope.
pub trait ScopedNode<'a>: ast::AcceptVisitor<'a> {}
impl<'a> ScopedNode<'a> for ast::Root<'a> {}
impl<'a> ScopedNode<'a> for ast::Module<'a> {}
impl<'a> ScopedNode<'a> for ast::Package<'a> {}

pub fn generated_scope<'gcx>(_cx: &impl Context<'gcx>, node: Ref<'gcx, impl ScopedNode<'gcx>>) {
    debug!("Generating scope");
    let mut gen = ScopeGenerator::default();
    node.accept(&mut gen);
}

/// A definition in a scope.
#[derive(Debug)]
pub struct Def<'a> {
    /// The node which defines the name.
    pub node: std::marker::PhantomData<&'a ()>,
    /// The name of the definition.
    pub name: Spanned<Name>,
    /// Where the definition is visible.
    pub vis: DefVis,
}

bitflags::bitflags! {
    /// Visibility of a definition.
    pub struct DefVis: u8 {
        /// Whether the definition is visible to local resolution, e.g. `foo`.
        const LOCAL = 1 << 0;
        /// Whether the definition is accessible in a hierarchical name, e.g.
        /// `parent.foo`.
        const HIERARCHICAL = 1 << 1;
        /// Whether the definition is accessible during namespace resolution,
        /// e.g. `parent::foo`.
        const NAMESPACE = 1 << 2;
    }
}

/// A visitor that gathers the contents of a scope from the AST.
#[derive(Default)]
struct ScopeGenerator;

impl ScopeGenerator {
    pub fn add_subscope<'a, 'b: 'a>(&mut self, node: &'a impl ScopedNode<'b>) {
        debug!("- Adding subscope");
    }

    pub fn add_def<'a>(&mut self, def: Def<'a>) {
        debug!("- Adding definition {:?}", def);
    }
}

impl<'a> ast::Visitor<'a> for ScopeGenerator {
    // We return `false` in the pre-visit functions when the visited node
    // generates a subscope, to avoid gobbling up its local definitions.

    fn pre_visit_root<'b: 'a>(&mut self, node: &'a ast::Root<'b>) -> bool {
        self.add_subscope(node);
        false
    }

    fn pre_visit_module<'b: 'a>(&mut self, node: &'a ast::Module<'b>) -> bool {
        debug!("- Adding module {}", node.name);
        self.add_subscope(node);
        self.add_def(Def {
            node: Default::default(),
            name: Spanned::new(node.name, node.name_span),
            vis: DefVis::LOCAL,
        });
        false
    }

    fn pre_visit_package<'b: 'a>(&mut self, node: &'a ast::Package<'b>) -> bool {
        debug!("- Adding package {}", node.name);
        self.add_subscope(node);
        self.add_def(Def {
            node: Default::default(),
            name: Spanned::new(node.name, node.name_span),
            vis: DefVis::LOCAL | DefVis::NAMESPACE,
        });
        false
    }

    fn pre_visit_import_item(&mut self, node: &'a ast::ImportItem) -> bool {
        debug!("- Adding import {}", node.span.extract());
        true
    }
}

/// Determine the location of a node within its enclosing scope.
pub fn scope_location<'a>(_cx: &impl Context<'a>, node: Ref<'a, impl ast::AnyNode<'a>>) {
    debug!("Scope location for a node");
}

/// A visitor that emits diagnostics for every resolved named.
pub struct ResolutionVisitor<'cx, C> {
    pub cx: &'cx C,
}

impl<'a, 'cx, C> ast::Visitor<'a> for ResolutionVisitor<'cx, C>
where
    C: Context<'a>,
    'a: 'cx,
{
    fn pre_visit_expr<'b: 'a>(&mut self, node: &'a ast::Expr<'b>) -> bool {
        match node.data {
            ast::IdentExpr(ident) => {
                debug!("Resolve `{}`", ident.name);
                // 1. Determine the scope location of the identifier.
                // scope_location(self.cx, node.into());
                // 1.1. Find the closest parent node which is a ScopedNode
                // 1.2. Combine with this node's lex_order
                // 2. Lookup the name at this scope location.
            }
            _ => (),
        }
        true
    }
}
