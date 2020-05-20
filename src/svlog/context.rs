// Copyright (c) 2016-2020 Fabian Schuiki

//! The central data structure of the compiler.
//!
//! The main piece of infrastructure provided by this module is the [`Context`]
//! trait. It exposes all queries supported by the compiler, together with many
//! other basic operations. Most compiler tasks interact only with [`Context`].
//! The complementary piece of the puzzle is the [`GlobalContext`] which caches
//! all intermediate results and implements the [`Context`] trait. The global
//! context also holds a reference to the [`GlobalArenas`] which own everything
//! that is allocated or interned during query execution.
//!
//! # Example
//!
//! ```
//! # use moore_common::Session;
//! # use moore_svlog::{GlobalContext, GlobalArenas};
//! let sess = Session::new();
//! let arena = GlobalArenas::default();
//! let gcx = GlobalContext::new(&sess, &arena);
//! ```

use crate::salsa; // TODO(fschuiki): Remove this once salsa is regular dep again
use crate::{
    ast,
    ast_map::{AstMap, AstNode},
    common::{arenas::Alloc, arenas::TypedArena, Session},
    crate_prelude::*,
    hir::{self, AccessTable, HirNode},
    resolver::StructDef,
    ty::{Type, TypeKind},
    typeck::{CastType, TypeContext},
    value::{Value, ValueData, ValueKind},
    InstDetails, InstTargetDetails, ParamEnv, ParamEnvData, ParamEnvSource, PortMapping,
    PortMappingSource,
};
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap, HashSet},
    sync::Arc,
};

/// The central data structure of the compiler. It stores references to various
/// arenas and tables that store the results of the various computations that
/// have been performed.
pub struct GlobalContext<'gcx> {
    /// The global compiler session.
    pub sess: &'gcx Session,
    /// The arena that owns all references.
    pub arena: &'gcx GlobalArenas<'gcx>,
    /// The underlying runtime for the query system.
    runtime: salsa::Runtime<GlobalContext<'gcx>>,
    /// The mapping of node IDs to abstract syntax tree nodes.
    ast_map: AstMap<'gcx>,
    /// The modules in the AST.
    modules: RefCell<HashMap<Name, NodeId>>,
    /// The packages in the AST.
    packages: RefCell<HashMap<Name, NodeId>>,
    /// A mapping from node ids to spans for diagnostics.
    node_id_to_span: RefCell<HashMap<NodeId, Span>>,
    /// The tables.
    tables: GlobalTables<'gcx>,
}

impl<'gcx> GlobalContext<'gcx> {
    /// Create a new global context.
    pub fn new(sess: &'gcx Session, arena: &'gcx GlobalArenas<'gcx>) -> Self {
        GlobalContext {
            sess,
            arena,
            runtime: Default::default(),
            ast_map: Default::default(),
            modules: Default::default(),
            packages: Default::default(),
            node_id_to_span: Default::default(),
            tables: Default::default(),
        }
    }

    /// Add root AST nodes to the context for processing.
    ///
    /// Use the `find_global_item` function afterwards to look up the id of
    /// modules that were added.
    pub fn add_root_nodes(&self, ast: impl Iterator<Item = &'gcx ast::Root<'gcx>>) {
        for root in ast {
            for item in &root.items {
                match *item {
                    ast::Item::ModuleDecl(ref m) => {
                        let id = self.map_ast(AstNode::Module(m));
                        self.modules.borrow_mut().insert(m.name, id);
                    }
                    ast::Item::PackageDecl(ref p) => {
                        let id = self.map_ast(AstNode::Package(p));
                        self.packages.borrow_mut().insert(p.name, id);
                    }
                    _ => {
                        let _: Result<()> = self.unimp(item);
                    }
                }
            }
        }
    }

    /// Find a module in the AST.
    pub fn find_module(&self, name: Name) -> Option<NodeId> {
        self.modules.borrow().get(&name).cloned()
    }

    /// Get an iterator over all modules in the AST.
    pub fn modules(&self) -> impl Iterator<Item = (Name, NodeId)> {
        self.modules.borrow().clone().into_iter()
    }

    /// Find a package in the AST.
    pub fn find_package(&self, name: Name) -> Option<NodeId> {
        self.packages.borrow().get(&name).cloned()
    }
}

impl DiagEmitter for GlobalContext<'_> {
    fn emit(&self, diag: DiagBuilder2) {
        let sev = diag.get_severity();
        self.sess.emit(diag);

        // If this is anything more than a warning, emit a backtrace in debug
        // builds.
        if sev >= Severity::Warning {
            trace!(
                "Diagnostic triggered here:\n{:?}",
                backtrace::Backtrace::new()
            );
        }
    }
}

impl<'gcx> salsa::Database for GlobalContext<'gcx> {
    fn salsa_runtime(&self) -> &salsa::Runtime<Self> {
        &self.runtime
    }
}

impl<'gcx> BaseContext<'gcx> for GlobalContext<'gcx> {
    fn gcx(&self) -> &GlobalContext<'gcx> {
        self
    }
}

/// The arenas that allocate things in the global context.
///
/// Use this struct whenever you want to allocate or internalize
/// something during the compilation procedure.
#[derive(Default)]
pub struct GlobalArenas<'t> {
    ids: TypedArena<NodeId>,
    hir: hir::Arena<'t>,
    param_envs: TypedArena<ParamEnvData<'t>>,
    ribs: TypedArena<Rib>,
    types: TypedArena<TypeKind<'t>>,
    values: TypedArena<ValueData<'t>>,
    mir_lvalue: TypedArena<mir::Lvalue<'t>>,
    mir_rvalue: TypedArena<mir::Rvalue<'t>>,
    /// Additional AST types generated during HIR lowering.
    ast_types: TypedArena<ast::Type<'t>>,
    /// Additional AST expressions generated during HIR lowering.
    ast_exprs: TypedArena<ast::Expr<'t>>,
}

impl<'t> GlobalArenas<'t> {
    /// Allocate a list of node IDs.
    pub fn alloc_ids(&'t self, ids: impl IntoIterator<Item = NodeId>) -> &'t [NodeId] {
        self.ids.alloc_extend(ids)
    }

    /// Allocate an HIR node into the global context.
    pub fn alloc_hir<T>(&'t self, hir: T) -> &'t T
    where
        hir::Arena<'t>: Alloc<'t, 't, T>,
        T: 't,
    {
        self.hir.alloc(hir)
    }

    /// Allocate a rib.
    pub fn alloc_rib(&'t self, rib: Rib) -> &'t Rib {
        self.ribs.alloc(rib)
    }

    /// Allocate an MIR lvalue.
    pub fn alloc_mir_lvalue(&'t self, mir: mir::Lvalue<'t>) -> &'t mir::Lvalue<'t> {
        self.mir_lvalue.alloc(mir)
    }

    /// Allocate an MIR rvalue.
    pub fn alloc_mir_rvalue(&'t self, mir: mir::Rvalue<'t>) -> &'t mir::Rvalue<'t> {
        self.mir_rvalue.alloc(mir)
    }

    /// Allocate an AST type.
    pub fn alloc_ast_type(&'t self, ast: ast::Type<'t>) -> &'t ast::Type {
        self.ast_types.alloc(ast)
    }

    /// Allocate an AST expression.
    pub fn alloc_ast_expr(&'t self, ast: ast::Expr<'t>) -> &'t ast::Expr {
        self.ast_exprs.alloc(ast)
    }
}

/// The lookup tables for a global context.
///
/// Use this struct whenever you need to keep track of some mapping.
#[derive(Default)]
pub struct GlobalTables<'t> {
    interned_param_envs: RefCell<HashMap<&'t ParamEnvData<'t>, ParamEnv>>,
    param_envs: RefCell<Vec<&'t ParamEnvData<'t>>>,
    param_env_contexts: RefCell<HashMap<ParamEnv, BTreeSet<NodeId>>>,
    node_id_to_parent_node_id: RefCell<HashMap<NodeId, NodeId>>,
    interned_types: RefCell<HashSet<Type<'t>>>,
    interned_values: RefCell<HashSet<Value<'t>>>,
    lowering_hints: RefCell<HashMap<NodeId, hir::Hint>>,
    interned_hir: RefCell<HashMap<NodeId, HirNode<'t>>>,
}

/// The fundamental compiler context.
///
/// This trait represents the context within which most compiler operations take
/// place. It is implemented by [`GlobalContext`] and also provides access to
/// the global context via the `gcx()` method.
pub trait BaseContext<'gcx>: salsa::Database + DiagEmitter {
    /// Get the global context.
    fn gcx(&self) -> &GlobalContext<'gcx>;

    /// Get the compiler session.
    fn sess(&self) -> &'gcx Session {
        self.gcx().sess
    }

    /// Access the arena into which values are to be allocated.
    fn arena(&self) -> &'gcx GlobalArenas<'gcx> {
        self.gcx().arena
    }

    /// Access the tables.
    fn tables(&self) -> &GlobalTables<'gcx> {
        &self.gcx().tables
    }

    /// Emit an internal compiler error that a node is not implemented.
    fn unimp<T: HasSpan + HasDesc, R>(&self, node: &T) -> Result<R> {
        self.emit(
            DiagBuilder2::bug(format!("{} not implemented", node.desc_full()))
                .span(node.human_span()),
        );
        Err(())
    }

    /// Emit an internal compiler error and message that a node is not
    /// implemented. Same as [`unimp`], but the caller can provide a message
    /// prefix.
    fn unimp_msg<T: HasSpan + HasDesc, R>(&self, msg: impl Into<String>, node: &T) -> Result<R> {
        self.emit(
            DiagBuilder2::bug(format!(
                "{} {} not implemented",
                msg.into(),
                node.desc_full()
            ))
            .span(node.human_span()),
        );
        Err(())
    }

    /// Allocate a new node id.
    ///
    /// The provided span is used primarily for diagnostic messages and is
    /// supposed to easily identify the node to the user in case of an error.
    fn alloc_id(&self, span: Span) -> NodeId {
        let id = NodeId::alloc();
        self.gcx().node_id_to_span.borrow_mut().insert(id, span);
        id
    }

    /// Return the diagnostic span associated with a ndoe id.
    fn span(&self, node_id: NodeId) -> Span {
        self.gcx()
            .node_id_to_span
            .borrow()
            .get(&node_id)
            .cloned()
            .unwrap_or(crate::common::source::INVALID_SPAN)
    }

    /// Associate an AST node with a node id.
    fn set_ast(&self, node_id: NodeId, ast: AstNode<'gcx>) {
        self.gcx().ast_map.set(node_id, ast)
    }

    /// Allocate a node id for an AST node and associate that id with the node.
    fn map_ast(&self, ast: AstNode<'gcx>) -> NodeId {
        let id = self.alloc_id(ast.human_span());
        self.set_ast(id, ast);
        id
    }

    /// Call [`map_ast`] and [`set_parent`].
    fn map_ast_with_parent(&self, ast: AstNode<'gcx>, parent: NodeId) -> NodeId {
        let id = self.map_ast(ast);
        self.set_parent(id, parent);
        id
    }

    /// Obtain the AST node associated with a node id.
    fn ast_of(&self, node_id: NodeId) -> Result<AstNode<'gcx>> {
        match self.gcx().ast_map.get(node_id) {
            Some(node) => Ok(node),
            None => {
                if let Some(&span) = self.gcx().node_id_to_span.borrow().get(&node_id) {
                    self.emit(
                        DiagBuilder2::bug(format!(
                            "no ast node for `{}` in the map",
                            span.extract()
                        ))
                        .span(span),
                    );
                } else {
                    self.emit(DiagBuilder2::bug(format!(
                        "no ast node for {:?} in the map",
                        node_id
                    )));
                }
                Err(())
            }
        }
    }

    /// Internalize an HIR node.
    fn intern_hir(&self, id: NodeId, hir: HirNode<'gcx>) {
        self.tables().interned_hir.borrow_mut().insert(id, hir);
    }

    /// Internalize an HIR node.
    fn intern_hir_with_parent(&self, id: NodeId, hir: HirNode<'gcx>, parent: NodeId) {
        self.intern_hir(id, hir);
        self.set_parent(id, parent);
    }

    /// Lookup an internalized HIR node.
    fn interned_hir(&self, id: NodeId) -> HirNode<'gcx> {
        self.tables().interned_hir.borrow()[&id]
    }

    /// Lookup an internalized HIR node.
    fn get_interned_hir(&self, id: NodeId) -> Option<HirNode<'gcx>> {
        self.tables().interned_hir.borrow().get(&id).cloned()
    }

    /// Internalize a type.
    fn intern_type(&self, ty: TypeKind<'gcx>) -> Type<'gcx> {
        if let Some(&x) = self.tables().interned_types.borrow().get(&ty) {
            return x;
        }
        let ty = self.arena().types.alloc(ty);
        self.tables().interned_types.borrow_mut().insert(ty);
        ty
    }

    /// Internalize a value.
    fn intern_value(&self, value: ValueData<'gcx>) -> Value<'gcx> {
        if let Some(&x) = self.tables().interned_values.borrow().get(&value) {
            return x;
        }
        let value = self.arena().values.alloc(value);
        self.tables().interned_values.borrow_mut().insert(value);
        value
    }

    /// Make a void type.
    fn mkty_void(&self) -> Type<'gcx> {
        &ty::VOID_TYPE
    }

    /// Make a time type.
    fn mkty_time(&self) -> Type<'gcx> {
        &ty::TIME_TYPE
    }

    /// Make a bit type.
    fn mkty_bit(&self) -> Type<'gcx> {
        &ty::BIT_TYPE
    }

    /// Make a logic type.
    fn mkty_logic(&self) -> Type<'gcx> {
        &ty::LOGIC_TYPE
    }

    /// Make a named type.
    fn mkty_named(&self, name: Spanned<Name>, binding: NodeEnvId) -> Type<'gcx> {
        self.intern_type(TypeKind::Named(
            name,
            binding.id(),
            self.gcx()
                .map_to_type(binding.id(), binding.env())
                .unwrap_or(&ty::ERROR_TYPE),
        ))
    }

    /// Make a 2-value integer type.
    fn mkty_int(&self, width: usize) -> Type<'gcx> {
        self.intern_type(TypeKind::Int(width, ty::Domain::TwoValued))
    }

    /// Make a 4-value integer type.
    fn mkty_integer(&self, width: usize) -> Type<'gcx> {
        self.intern_type(TypeKind::Int(width, ty::Domain::FourValued))
    }

    /// Make a struct type.
    fn mkty_struct(&self, def_id: NodeId) -> Type<'gcx> {
        self.intern_type(TypeKind::Struct(def_id))
    }

    /// Make a packed array type.
    fn mkty_packed_array(&self, size: usize, elem_ty: Type<'gcx>) -> Type<'gcx> {
        self.intern_type(TypeKind::PackedArray(size, elem_ty))
    }

    /// Internalize a parameter environment.
    fn intern_param_env(&self, env: ParamEnvData<'gcx>) -> ParamEnv {
        if let Some(&x) = self.tables().interned_param_envs.borrow().get(&env) {
            return x;
        }
        let data = self.arena().param_envs.alloc(env);
        let id = {
            let mut vec = self.tables().param_envs.borrow_mut();
            let id = ParamEnv(vec.len() as u32);
            vec.push(data);
            id
        };
        self.tables()
            .interned_param_envs
            .borrow_mut()
            .insert(data, id);
        id
    }

    /// Get the [`ParamEnvData`] associated with a [`ParamEnv`].
    fn param_env_data(&self, env: ParamEnv) -> &'gcx ParamEnvData<'gcx> {
        self.tables().param_envs.borrow()[env.0 as usize]
    }

    /// Get the default parameter environment.
    ///
    /// This is useful for instantiations without any parameter assignment, e.g.
    /// for the top-level module.
    fn default_param_env(&self) -> ParamEnv {
        self.intern_param_env(ParamEnvData::default())
    }

    /// Associate a context with a param env.
    ///
    /// A context in this sense is the node that the param env relates to.
    /// Usually this is the node that actually generated the param env, e.g. a
    /// module instantiation.
    fn add_param_env_context(&self, env: ParamEnv, context: NodeId) {
        self.tables()
            .param_env_contexts
            .borrow_mut()
            .entry(env)
            .or_insert_with(Default::default)
            .insert(context);
    }

    /// Get the contexts associated with a parameter environment.
    ///
    /// Returns what has previously been added with `add_param_env_context`.
    fn param_env_contexts(&self, env: ParamEnv) -> Vec<NodeId> {
        self.tables()
            .param_env_contexts
            .borrow()
            .get(&env)
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_else(Default::default)
    }

    /// Associate a parent with a node.
    ///
    /// Panics if `node_id` already has a parent assigned.
    fn set_parent(&self, node_id: NodeId, parent_id: NodeId) {
        if let Some(old_id) = self
            .tables()
            .node_id_to_parent_node_id
            .borrow_mut()
            .insert(node_id, parent_id)
        {
            panic!(
                "node {:?} already had parent {:?} (overwritten with {:?} now)",
                node_id, old_id, parent_id
            );
        }
    }

    /// Find the parent node of a node.
    ///
    /// Returns `None` if the node has no parent. Pretty much every node has a
    /// parent, assigned more or less in lexographical order.
    fn parent_node_id(&self, node_id: NodeId) -> Option<NodeId> {
        self.tables()
            .node_id_to_parent_node_id
            .borrow()
            .get(&node_id)
            .cloned()
    }

    /// Check if a node is the parent of another.
    fn is_parent_of(&self, parent_id: NodeId, child_id: NodeId) -> bool {
        if parent_id == child_id {
            true
        } else {
            match self.parent_node_id(child_id) {
                Some(id) => self.is_parent_of(parent_id, id),
                None => false,
            }
        }
    }

    /// Resolve a name upwards or emit a diagnostic if nothing is found.
    fn resolve_upwards_or_error(&self, name: Spanned<Name>, start_at: NodeId) -> Result<NodeId> {
        match self.gcx().resolve_upwards(name.value, start_at)? {
            Some(id) => Ok(id),
            None => {
                self.emit(
                    DiagBuilder2::error(format!("`{}` not found", name.value)).span(name.span),
                );
                Err(())
            }
        }
    }

    /// Resolve a name downwards or emit a diagnostic if nothing is found.
    fn resolve_downwards_or_error(&self, name: Spanned<Name>, start_at: NodeId) -> Result<NodeId> {
        match self.gcx().resolve_downwards(name.value, start_at)? {
            Some(id) => Ok(id),
            None => {
                self.emit(
                    DiagBuilder2::error(format!(
                        "`{}` not found in {}",
                        name.value,
                        self.ast_of(start_at)?.desc_full()
                    ))
                    .span(name.span),
                );
                Err(())
            }
        }
    }

    /// Set a lowering hint on a node.
    fn set_lowering_hint(&self, node_id: NodeId, hint: hir::Hint) {
        self.tables()
            .lowering_hints
            .borrow_mut()
            .insert(node_id, hint);
    }

    /// Get a lowering hint on a node.
    fn lowering_hint(&self, node_id: NodeId) -> Option<hir::Hint> {
        self.tables().lowering_hints.borrow().get(&node_id).cloned()
    }

    /// Compute the constant value of a node and make sure it is an integer.
    fn constant_int_value_of(&self, node_id: NodeId, env: ParamEnv) -> Result<&'gcx num::BigInt> {
        match self.gcx().constant_value_of(node_id, env)?.kind {
            ValueKind::Int(ref x, ..) => Ok(x),
            _ => {
                let hir = self.gcx().hir_of(node_id)?;
                self.emit(
                    DiagBuilder2::error(format!("{} is not a constant integer", hir.desc_full()))
                        .span(hir.human_span()),
                );
                Err(())
            }
        }
    }
}

/// The queries implemented by the compiler.
pub(super) mod queries {
    use super::*;

    query_group! {
        /// A collection of compiler queries.
        pub trait Context<'a>: BaseContext<'a> {
            /// Lower an AST node to HIR.
            fn hir_of(node_id: NodeId) -> Result<HirNode<'a>> {
                type HirOfQuery;
                use fn hir::hir_of;
            }

            /// Compute the parameter bindings for an instantiation.
            fn param_env(src: ParamEnvSource<'a>) -> Result<ParamEnv> {
                type ParamEnvQuery;
                use fn param_env::compute;
            }

            /// Determine the type of a node.
            fn type_of(node_id: NodeId, env: ParamEnv) -> Result<Type<'a>> {
                type TypeOfQuery;
                use fn typeck::type_of;
            }

            /// Convert a node to a type.
            fn map_to_type(node_id: NodeId, env: ParamEnv) -> Result<Type<'a>> {
                type MapToTypeQuery;
                use fn typeck::map_to_type;
            }

            /// Get the cast type of a node.
            fn cast_type(node_id: NodeId, env: ParamEnv) -> Option<CastType<'a>> {
                type CastTypeQuery;
                use fn typeck::cast_type;
            }

            /// Get the self-determined type of a node.
            fn self_determined_type(node_id: NodeId, env: ParamEnv) -> Option<Type<'a>> {
                type SelfDeterminedTypeQuery;
                use fn typeck::self_determined_type;
            }

            /// Require a node to have a self-determined type.
            ///
            /// Emits an error if the node has no self-determined type.
            fn need_self_determined_type(node_id: NodeId, env: ParamEnv) -> Type<'a> {
                type NeedSelfDeterminedTypeQuery;
                use fn typeck::need_self_determined_type;
            }

            /// Get the operation type of an expression.
            fn operation_type(node_id: NodeId, env: ParamEnv) -> Option<Type<'a>> {
                type OperationTypeQuery;
                use fn typeck::operation_type;
            }

            /// Require a node to have an operation type.
            ///
            /// Emits an error if the node has no operation type.
            fn need_operation_type(node_id: NodeId, env: ParamEnv) -> Type<'a> {
                type NeedOperationTypeQuery;
                use fn typeck::need_operation_type;
            }

            /// Get the type context of a node.
            fn type_context(node_id: NodeId, env: ParamEnv) -> Option<TypeContext<'a>> {
                type TypeContextQuery;
                use fn typeck::type_context;
            }

            /// Require a node to have a type context.
            ///
            /// Emits an error if the node has no type context.
            fn need_type_context(node_id: NodeId, env: ParamEnv) -> TypeContext<'a> {
                type NeedTypeContextQuery;
                use fn typeck::need_type_context;
            }

            /// Determine the local rib that applies to a node.
            fn local_rib(node_id: NodeId) -> Result<&'a Rib> {
                type LocalRibQuery;
                use fn resolver::local_rib;
            }

            /// Determine the hierarchical rib of a node.
            fn hierarchical_rib(node_id: NodeId) -> Result<&'a Rib> {
                type HierarchicalRibQuery;
                use fn resolver::hierarchical_rib;
            }

            /// Resolve a name upwards through the ribs.
            fn resolve_upwards(name: Name, start_at: NodeId) -> Result<Option<NodeId>> {
                type ResolveUpwardsQuery;
                use fn resolver::resolve_upwards;
            }

            /// Resolve a name downwards through the ribs.
            fn resolve_downwards(name: Name, start_at: NodeId) -> Result<Option<NodeId>> {
                type ResolveDownwardsQuery;
                use fn resolver::resolve_downwards;
            }

            /// Resolve a node to its target.
            fn resolve_node(node_id: NodeId, env: ParamEnv) -> Result<NodeId> {
                type ResolveNodeQuery;
                use fn resolver::resolve_node;
            }

            /// Determine the constant value of a node.
            fn constant_value_of(node_id: NodeId, env: ParamEnv) -> Result<Value<'a>> {
                type ConstantValueOfQuery;
                use fn value::constant_value_of;
            }

            /// Check if a node has a constant value.
            fn is_constant(node_id: NodeId) -> Result<bool> {
                type IsConstantQuery;
                use fn value::is_constant;
            }

            /// Determine the default value of a type.
            fn type_default_value(ty: Type<'a>) -> Value<'a> {
                type TypeDefaultValueQuery;
                use fn value::type_default_value;
            }

            /// Determine the nodes accessed by another node.
            fn accessed_nodes(node_id: NodeId) -> Result<Arc<AccessTable>> {
                type AccessedNodesQuery;
                use fn  hir::accessed_nodes;
            }

            /// Compute the port assignments for an instantiation.
            fn port_mapping(src: PortMappingSource<'a>) -> Result<Arc<PortMapping>> {
                type PortMappingQuery;
                use fn port_mapping::compute;
            }

            /// Obtain the details of a struct definition.
            fn struct_def(node_id: NodeId) -> Result<Arc<StructDef>> {
                type StructDefQuery;
                use fn resolver::struct_def;
            }

            /// Resolve the field name in a field access expression.
            ///
            /// Returns the node id of the corresponding struct definition, the
            /// index of the field that is actually being accessed, and the node
            /// id of the field definition.
            fn resolve_field_access(node_id: NodeId, env: ParamEnv) -> Result<(NodeId, usize, NodeId)> {
                type ResolveFieldAccessQuery;
                use fn resolver::resolve_field_access;
            }

            /// Lower an expression to an lvalue in the MIR.
            fn mir_lvalue(
                expr_id: NodeId,
                env: ParamEnv,
            ) -> &'a mir::Lvalue<'a> {
                type MirLvalueQuery;
                use fn mir::lower::lvalue::lower_expr;
            }

            /// Lower an expression to an rvalue in the MIR.
            fn mir_rvalue(
                expr_id: NodeId,
                env: ParamEnv,
            ) -> &'a mir::Rvalue<'a> {
                type MirRvalueQuery;
                use fn mir::lower::rvalue::lower_expr;
            }

            /// Determine the details of an instantiation.
            fn inst_details(inst: NodeEnvId) -> Result<Arc<InstDetails<'a>>> {
                type InstDetailsQuery;
                use fn crate::inst_details::compute_inst;
            }

            /// Determine the details of an instantiation target.
            fn inst_target_details(inst: NodeEnvId) -> Result<Arc<InstTargetDetails<'a>>> {
                type InstTargetDetailsQuery;
                use fn crate::inst_details::compute_inst_target;
            }
        }
    }

    database_storage! {
        /// The query result storage embedded in the global context.
        pub struct GlobalStorage<'gcx> for GlobalContext<'gcx> {
            impl Context<'gcx> {
                fn hir_of() for HirOfQuery<'gcx>;
                fn param_env() for ParamEnvQuery<'gcx>;
                fn type_of() for TypeOfQuery<'gcx>;
                fn map_to_type() for MapToTypeQuery<'gcx>;
                fn cast_type() for CastTypeQuery<'gcx>;
                fn self_determined_type() for SelfDeterminedTypeQuery<'gcx>;
                fn need_self_determined_type() for NeedSelfDeterminedTypeQuery<'gcx>;
                fn operation_type() for OperationTypeQuery<'gcx>;
                fn need_operation_type() for NeedOperationTypeQuery<'gcx>;
                fn type_context() for TypeContextQuery<'gcx>;
                fn need_type_context() for NeedTypeContextQuery<'gcx>;
                fn local_rib() for LocalRibQuery<'gcx>;
                fn hierarchical_rib() for HierarchicalRibQuery<'gcx>;
                fn resolve_upwards() for ResolveUpwardsQuery<'gcx>;
                fn resolve_downwards() for ResolveDownwardsQuery<'gcx>;
                fn constant_value_of() for ConstantValueOfQuery<'gcx>;
                fn is_constant() for IsConstantQuery<'gcx>;
                fn type_default_value() for TypeDefaultValueQuery<'gcx>;
                fn resolve_node() for ResolveNodeQuery<'gcx>;
                fn accessed_nodes() for AccessedNodesQuery<'gcx>;
                fn port_mapping() for PortMappingQuery<'gcx>;
                fn struct_def() for StructDefQuery<'gcx>;
                fn resolve_field_access() for ResolveFieldAccessQuery<'gcx>;
                fn mir_lvalue() for MirLvalueQuery<'gcx>;
                fn mir_rvalue() for MirRvalueQuery<'gcx>;
                fn inst_details() for InstDetailsQuery<'gcx>;
                fn inst_target_details() for InstTargetDetailsQuery<'gcx>;
            }
        }
    }
}

pub use self::queries::Context;
