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

use crate::crate_prelude::*;
use crate::salsa; // TODO(fschuiki): Remove this once salsa is regular dep again
use crate::{
    ast::{self, Visitor},
    ast_map::{AstMap, AstNode},
    common::{arenas::Alloc, arenas::TypedArena, Session},
    hir::{self, HirNode},
    port_list::PortList,
    resolver::{Scope, StructDef},
    value::{Value, ValueData, ValueKind},
    ParamEnv, ParamEnvData, QueryDatabase, QueryStorage,
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
    /// The underlying storage for the new query system.
    storage: QueryStorage<'gcx>,
    /// The mapping of node IDs to abstract syntax tree nodes.
    ast_map: AstMap<'gcx>,
    /// The AST nodes.
    ast_map2: RefCell<HashMap<NodeId, &'gcx dyn ast::AnyNode<'gcx>>>,
    /// The modules in the AST.
    modules: RefCell<HashMap<Name, NodeId>>,
    /// The packages in the AST.
    packages: RefCell<HashMap<Name, NodeId>>,
    /// The interfaces in the AST.
    interfaces: RefCell<HashMap<Name, NodeId>>,
    /// The global imports in the AST.
    imports: RefCell<Vec<NodeId>>,
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
            storage: Default::default(),
            ast_map: Default::default(),
            ast_map2: Default::default(),
            modules: Default::default(),
            packages: Default::default(),
            interfaces: Default::default(),
            imports: Default::default(),
            node_id_to_span: Default::default(),
            tables: Default::default(),
        }
    }

    /// Add an AST root to the context for processing.
    ///
    /// Use the `find_global_item` function afterwards to look up the id of
    /// modules that were added.
    pub fn add_root(&self, root: &'gcx ast::Root<'gcx>) {
        debug!("Linking nodes");
        let mut index = 0;
        root.link(None, &mut index);
        debug!("Linked {} nodes", index);

        // Ensure there are no naming conflicts in the scopes.
        debug!("Materializing scopes");
        crate::resolver::materialize_scope(self, root);

        // Register nodes with the AST map. This is a necessary hack until
        // we have moved away from querying nodes merely by ID.
        self.register_ast(root);

        // Resolve names for debugging purposes.
        debug!("Checking names");
        self.nameck(root);

        // Keep track of some names for now.
        for file in &root.files {
            for item in &file.items {
                match &item.data {
                    ast::ItemData::ModuleDecl(ref n) => {
                        let id = self.map_ast(AstNode::Module(n));
                        self.modules.borrow_mut().insert(n.name.value, id);
                    }
                    ast::ItemData::PackageDecl(ref n) => {
                        let id = self.map_ast(AstNode::Package(n));
                        self.packages.borrow_mut().insert(n.name.value, id);
                    }
                    ast::ItemData::InterfaceDecl(ref n) => {
                        let id = self.map_ast(AstNode::Interface(n));
                        self.interfaces.borrow_mut().insert(n.name.value, id);
                    }
                    ast::ItemData::ImportDecl(ref n) => {
                        for item in &n.items {
                            let id = self.map_ast(AstNode::Import(item));
                            self.imports.borrow_mut().push(id);
                        }
                    }
                    _ => (),
                }
            }
        }

        debug!("{:?} added", root);
    }

    /// Add an AST root with a series of source files to the context for
    /// processing.
    pub fn add_files(&self, files: impl Iterator<Item = &'gcx ast::SourceFile<'gcx>>) {
        let root = ast::Root::new(
            moore_common::source::INVALID_SPAN,
            ast::RootData {
                files: files.collect(),
            },
        );
        let root = self.arena.alloc_ast_root(root);
        self.add_root(root);
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

    /// Get an iterator over all root imports in the AST.
    pub fn imports(&self) -> impl Iterator<Item = NodeId> {
        self.imports.borrow().clone().into_iter()
    }
}

impl DiagEmitter for GlobalContext<'_> {
    fn emit(&self, mut diag: DiagBuilder2) {
        let sev = diag.get_severity();

        // Extend the diagnostic with some context information as to where in
        // the query stack it occurred.
        if sev >= Severity::Error {
            for query in self.storage().stack.borrow().iter().rev() {
                match query {
                    QueryTag::TypeOfExpr(query) => {
                        diag = diag
                            .add_note("Needed to compute the type of the expression:")
                            .span(query.0.span());
                    }
                    QueryTag::TypeOfIntPort(query) => {
                        diag = diag
                            .add_note(format!(
                                "Needed to compute the type of port `{}`:",
                                query.0.name
                            ))
                            .span(query.0.span);
                    }
                    QueryTag::TypeOfVarDecl(query) => {
                        diag = diag
                            .add_note(format!(
                                "Needed to compute the type of variable `{}`:",
                                query.0.name
                            ))
                            .span(query.0.span);
                    }
                    _ => (),
                }
            }
        }

        // Emit the diagnostic.
        self.sess.emit(diag);

        // If this is anything more than a warning, emit a backtrace in debug
        // builds.
        if sev >= Severity::Warning {
            trace!("Diagnostic query trace:");
            for x in self.storage().stack.borrow().iter().rev() {
                trace!(" - {:?}", x);
            }
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

impl<'gcx> QueryDatabase<'gcx> for GlobalContext<'gcx> {
    type Context = Self;

    fn context(&self) -> &Self {
        self
    }

    fn storage(&self) -> &QueryStorage<'gcx> {
        &self.storage
    }
}

impl<'gcx> ty::HasTypeStorage<'gcx> for GlobalContext<'gcx> {
    fn type_storage(&self) -> &'gcx ty::TypeStorage<'gcx> {
        &self.arena.type_storage
    }
}

/// The arenas that allocate things in the global context.
///
/// Use this struct whenever you want to allocate or internalize
/// something during the compilation procedure.
#[derive(Default)]
pub struct GlobalArenas<'t> {
    ids: TypedArena<NodeId>,
    pub ast: ast::Arena<'t>,
    hir: hir::Arena<'t>,
    param_envs: TypedArena<ParamEnvData<'t>>,
    ribs: TypedArena<Rib>,
    port_lists: TypedArena<PortList<'t>>,
    scopes: TypedArena<Scope<'t>>,
    values: TypedArena<ValueData<'t>>,
    mir_lvalue: TypedArena<mir::Lvalue<'t>>,
    mir_rvalue: TypedArena<mir::Rvalue<'t>>,
    mir_assignment: TypedArena<mir::Assignment<'t>>,
    ast_roots: TypedArena<ast::Root<'t>>,
    /// Additional AST types generated during HIR lowering.
    ast_types: TypedArena<ast::Type<'t>>,
    /// Additional AST expressions generated during HIR lowering.
    ast_exprs: TypedArena<ast::Expr<'t>>,
    /// The underlying storage for type operations.
    type_storage: ty::TypeStorage<'t>,
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

    /// Allocate a port list.
    pub fn alloc_port_list(&'t self, port_list: PortList<'t>) -> &'t PortList<'t> {
        self.port_lists.alloc(port_list)
    }

    /// Allocate a scope.
    pub fn alloc_scope(&'t self, scope: Scope<'t>) -> &'t Scope<'t> {
        self.scopes.alloc(scope)
    }

    /// Allocate an MIR lvalue.
    pub fn alloc_mir_lvalue(&'t self, mir: mir::Lvalue<'t>) -> &'t mir::Lvalue<'t> {
        self.mir_lvalue.alloc(mir)
    }

    /// Allocate an MIR rvalue.
    pub fn alloc_mir_rvalue(&'t self, mir: mir::Rvalue<'t>) -> &'t mir::Rvalue<'t> {
        self.mir_rvalue.alloc(mir)
    }

    /// Allocate an MIR assignment.
    pub fn alloc_mir_assignment(&'t self, mir: mir::Assignment<'t>) -> &'t mir::Assignment<'t> {
        self.mir_assignment.alloc(mir)
    }

    /// Allocate an AST root.
    pub fn alloc_ast_root(&'t self, ast: ast::Root<'t>) -> &'t ast::Root {
        self.ast_roots.alloc(ast)
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

/// Allow AST nodes to be allocated into `GlobalArenas`.
impl<'t, T: 't> Alloc<'t, 't, T> for GlobalArenas<'t>
where
    ast::Arena<'t>: Alloc<'t, 't, T>,
{
    fn alloc(&'t self, value: T) -> &'t mut T {
        self.ast.alloc(value)
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
    interned_values: RefCell<HashSet<Value<'t>>>,
    lowering_hints: RefCell<HashMap<NodeId, hir::Hint>>,
    interned_hir: RefCell<HashMap<NodeId, HirNode<'t>>>,
}

/// The fundamental compiler context.
///
/// This trait represents the context within which most compiler operations take
/// place. It is implemented by [`GlobalContext`] and also provides access to
/// the global context via the `gcx()` method.
pub trait BaseContext<'gcx>:
    salsa::Database + DiagEmitter + QueryDatabase<'gcx> + ty::HasTypeStorage<'gcx>
{
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
        self.set_span(id, span);
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

    /// Associate a span with a node id.
    fn set_span(&self, node_id: NodeId, span: Span) {
        self.gcx()
            .node_id_to_span
            .borrow_mut()
            .insert(node_id, span);
    }

    /// Associate an AST node with a node id.
    fn set_ast(&self, node_id: NodeId, ast: AstNode<'gcx>) {
        self.gcx().ast_map.set(node_id, ast);
        if let Some(any) = ast.get_any() {
            self.gcx().ast_map2.borrow_mut().insert(node_id, any);
        }
    }

    /// Allocate a node id for an AST node and associate that id with the node.
    fn map_ast(&self, ast: AstNode<'gcx>) -> NodeId {
        let id = match ast.get_any() {
            Some(node) => {
                self.set_span(node.id(), node.human_span());
                node.id()
            }
            None => self.alloc_id(ast.human_span()),
        };
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
            Some(node) => return Ok(node),
            None => (),
        }
        let other = self.ast_for_id(node_id);
        match AstNode::from_all(other.as_all()).next() {
            Some(node) => return Ok(node),
            None => (),
        }
        if let Some(&span) = self.gcx().node_id_to_span.borrow().get(&node_id) {
            self.emit(
                DiagBuilder2::bug(format!("no ast node for `{}` in the map", span.extract()))
                    .span(span),
            );
            error!("Offending node: {:?}", node_id);
        } else {
            self.emit(DiagBuilder2::bug(format!(
                "no ast node for {:?} in the map",
                node_id
            )));
        }
        panic!("Other map contains: {:?}", other);
    }

    /// Register an `ast::AnyNode` for later retrieval by ID.
    fn register_ast(&self, node: &'gcx dyn ast::AnyNode<'gcx>) {
        let mut visitor = AstMapRegistrator { cx: self.gcx() };
        visitor.pre_visit_node(node);
        node.accept(&mut visitor);
        visitor.post_visit_node(node);
    }

    /// Obtain an `ast::AnyNode` associated with a node id.
    fn ast_for_id(&self, node_id: NodeId) -> &'gcx dyn ast::AnyNode<'gcx> {
        match self.gcx().ast_map2.borrow().get(&node_id) {
            Some(&node) => node,
            None => panic!("no AST node for {:?} registered", node_id),
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

    /// Internalize a value.
    fn intern_value(&self, value: ValueData<'gcx>) -> Value<'gcx> {
        if let Some(&x) = self.tables().interned_values.borrow().get(&value) {
            return x;
        }
        let value = self.arena().values.alloc(value);
        self.tables().interned_values.borrow_mut().insert(value);
        value
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
        self.tables()
            .node_id_to_parent_node_id
            .borrow_mut()
            .insert(node_id, parent_id);
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
        match self.gcx().constant_value_of(node_id, env).kind {
            ValueKind::Int(ref x, ..) => Ok(x),
            ValueKind::Error => Err(()),
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

            /// Obtain the details of a struct definition.
            fn struct_def(node_id: NodeId) -> Result<Arc<StructDef>> {
                type StructDefQuery;
                use fn resolver::struct_def;
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
        }
    }

    database_storage! {
        /// The query result storage embedded in the global context.
        pub struct GlobalStorage<'gcx> for GlobalContext<'gcx> {
            impl Context<'gcx> {
                fn hir_of() for HirOfQuery<'gcx>;
                fn local_rib() for LocalRibQuery<'gcx>;
                fn hierarchical_rib() for HierarchicalRibQuery<'gcx>;
                fn resolve_upwards() for ResolveUpwardsQuery<'gcx>;
                fn resolve_downwards() for ResolveDownwardsQuery<'gcx>;
                fn resolve_node() for ResolveNodeQuery<'gcx>;
                fn struct_def() for StructDefQuery<'gcx>;
                fn mir_lvalue() for MirLvalueQuery<'gcx>;
                fn mir_rvalue() for MirRvalueQuery<'gcx>;
            }
        }
    }
}

pub use self::queries::Context;

/// An ugly hack to get the new AST nodes to hook into the ID-based AST lookup
/// during the transition phase.
struct AstMapRegistrator<'a, 'b> {
    cx: &'b GlobalContext<'a>,
}

impl<'a, 'b> ast::Visitor<'a> for AstMapRegistrator<'a, 'b> {
    fn post_visit_node(&mut self, node: &'a dyn ast::AnyNode<'a>) {
        self.cx.gcx().ast_map2.borrow_mut().insert(node.id(), node);

        for n in AstNode::from_all(node.as_all()) {
            let parent = n.get_any().unwrap().get_parent().unwrap();
            let parent = if let Some(kind) = parent.as_all().get_type_kind() {
                kind.get_parent().unwrap()
            } else {
                parent
            };
            self.cx.map_ast_with_parent(n, parent.id());
        }
    }

    fn post_visit_module(&mut self, node: &'a ast::Module<'a>) {
        // Ensure the ports are added to the AST map. Pretty ugly, but necessary.
        self.cx.canonicalize_ports(node);
    }

    fn post_visit_interface(&mut self, node: &'a ast::Interface<'a>) {
        // Ensure the ports are added to the AST map. Pretty ugly, but necessary.
        self.cx.canonicalize_ports(node);
    }
}
