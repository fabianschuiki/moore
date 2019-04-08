// Copyright (c) 2016-2019 Fabian Schuiki

//! Name resolution.
//!
//! This module implements the infrastructure to describe scopes and resolve
//! names in them.

use crate::{ast_map::AstNode, crate_prelude::*, hir::HirNode, ty::TypeKind, ParamEnv};
use std::collections::HashMap;

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
}

impl Rib {
    /// Look up a name.
    pub fn get(&self, name: Name) -> Option<NodeId> {
        self.kind.get(name)
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
        AstNode::VarDecl(decl, _, _) => Some(RibKind::Normal(
            Spanned::new(decl.name, decl.name_span),
            node_id,
        )),
        AstNode::GenvarDecl(decl) => Some(RibKind::Normal(
            Spanned::new(decl.name, decl.name_span),
            node_id,
        )),
        AstNode::Port(&ast::Port::Named { name, .. }) => {
            Some(RibKind::Normal(Spanned::new(name.name, name.span), node_id))
        }
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
        AstNode::Type(ty) => match ty.data {
            ast::EnumType(..) => {
                let hir = match cx.hir_of(node_id)? {
                    HirNode::Type(x) => x,
                    _ => unreachable!(),
                };
                match hir.kind {
                    hir::TypeKind::Enum(ref variants, _) => Some(RibKind::Enum(
                        variants
                            .iter()
                            .map(|(name, id)| (name.value, *id))
                            .collect(),
                    )),
                    _ => None,
                }
            }
            _ => None,
        },
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
    Ok(cx.arena().alloc_rib(rib))
}

/// Determine the hierarchical rib of a node.
///
/// This will return a rib containing the hierarchical names expose by a node.
pub(crate) fn hierarchical_rib<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
) -> Result<&'gcx Rib> {
    let hir = cx.hir_of(node_id)?;
    let mut names = HashMap::new();
    let mut rib_id = match hir {
        HirNode::Package(pkg) => Some(pkg.last_rib),
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
    let mut next_id = Some(start_at);
    while let Some(rib_id) = next_id {
        let rib = cx.local_rib(rib_id)?;
        if let id @ Some(_) = rib.get(name) {
            return Ok(id);
        }
        next_id = rib.parent;
    }
    if let m @ Some(_) = cx.gcx().find_module(name) {
        return Ok(m);
    }
    if let p @ Some(_) = cx.gcx().find_package(name) {
        return Ok(p);
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
        _ => (),
    }
    panic!("cannot resolve {:?}", hir)
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
    let struct_def = match ty {
        &TypeKind::Struct(id) => id,
        &TypeKind::Named(_, _, &TypeKind::Struct(id)) => id,
        _ => {
            let hir = cx.hir_of(target_id)?;
            cx.emit(
                DiagBuilder2::error(format!("{} is not a struct", hir.desc_full()))
                    .span(hir.human_span()),
            );
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
