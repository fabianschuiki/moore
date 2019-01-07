// Copyright (c) 2016-2019 Fabian Schuiki

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
//! # extern crate moore_common as common;
//! # extern crate moore_svlog as svlog;
//! # use common::Session;
//! # use svlog::{GlobalContext, GlobalArenas};
//! let sess = Session::new();
//! let arena = GlobalArenas::default();
//! let gcx = GlobalContext::new(&sess, &arena);
//! ```

use crate::{
    ast,
    ast_map::{AstMap, AstNode},
    common::{arenas::Alloc, arenas::TypedArena, Session},
    crate_prelude::*,
    hir::{self, HirNode},
    ty::{Type, TypeKind},
    ParamEnv, ParamEnvData, ParamEnvSource,
};
use llhd;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
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
            node_id_to_span: Default::default(),
            tables: Default::default(),
        }
    }

    /// Add root AST nodes to the context for processing.
    ///
    /// Use the `find_global_item` function afterwards to look up the id of
    /// modules that were added.
    pub fn add_root_nodes(&self, ast: impl Iterator<Item = &'gcx ast::Root>) {
        for root in ast {
            for item in &root.items {
                match *item {
                    ast::Item::Module(ref m) => {
                        let id = self.map_ast(AstNode::Module(m));
                        self.modules.borrow_mut().insert(m.name, id);
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
}

impl DiagEmitter for GlobalContext<'_> {
    fn emit(&self, diag: DiagBuilder2) {
        self.sess.emit(diag)
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
pub struct GlobalArenas<'t> {
    ids: TypedArena<NodeId>,
    hir: hir::Arena<'t>,
    param_envs: TypedArena<ParamEnvData>,
    ribs: TypedArena<Rib>,
    types: TypedArena<TypeKind<'t>>,
}

impl Default for GlobalArenas<'_> {
    fn default() -> Self {
        GlobalArenas {
            ids: TypedArena::new(),
            hir: Default::default(),
            param_envs: TypedArena::new(),
            ribs: TypedArena::new(),
            types: TypedArena::new(),
        }
    }
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
}

/// The lookup tables for a global context.
///
/// Use this struct whenever you need to keep track of some mapping.
#[derive(Default)]
pub struct GlobalTables<'t> {
    interned_param_envs: RefCell<HashMap<&'t ParamEnvData, ParamEnv>>,
    param_envs: RefCell<Vec<&'t ParamEnvData>>,
    node_id_to_parent_node_id: RefCell<HashMap<NodeId, NodeId>>,
    interned_types: RefCell<HashSet<Type<'t>>>,
}

/// The fundamental compiler context.
///
/// This trait represents the context within which most compiler operations take
/// place. It is implemented by [`GlobalContext`] and also provides access to
/// the global context via the `gcx()` method.
pub trait BaseContext<'gcx>: salsa::Database + DiagEmitter {
    /// Get the global context.
    #[inline(always)]
    fn gcx(&self) -> &GlobalContext<'gcx>;

    /// Get the compiler session.
    #[inline(always)]
    fn sess(&self) -> &'gcx Session {
        self.gcx().sess
    }

    /// Access the arena into which values are to be allocated.
    #[inline(always)]
    fn arena(&self) -> &'gcx GlobalArenas<'gcx> {
        self.gcx().arena
    }

    /// Access the tables.
    #[inline(always)]
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

    /// Obtain the AST node associated with a node id.
    fn ast_of(&self, node_id: NodeId) -> Result<AstNode<'gcx>> {
        match self.gcx().ast_map.get(node_id) {
            Some(node) => Ok(node),
            None => {
                let span = self.gcx().node_id_to_span.borrow()[&node_id];
                self.emit(
                    DiagBuilder2::bug(format!("no ast node for `{}` in the map", span.extract()))
                        .span(span),
                );
                Err(())
            }
        }
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

    /// Make a void type.
    fn mkty_void(&self) -> Type<'gcx> {
        static STATIC: TypeKind<'static> = TypeKind::Void;
        &STATIC
    }

    /// Make a bit type.
    fn mkty_bit(&self) -> Type<'gcx> {
        static STATIC: TypeKind<'static> = TypeKind::Bit;
        &STATIC
    }

    /// Make a named type.
    fn mkty_named(&self, name: Spanned<Name>, binding: NodeEnvId) -> Type<'gcx> {
        self.intern_type(TypeKind::Named(
            name,
            binding.0,
            self.gcx()
                .map_to_type(binding.0, binding.1)
                .unwrap_or(self.mkty_void()),
        ))
    }

    /// Internalize a parameter environment.
    fn intern_param_env(&self, env: ParamEnvData) -> ParamEnv {
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
    fn param_env_data(&self, env: ParamEnv) -> &'gcx ParamEnvData {
        self.tables().param_envs.borrow()[env.0 as usize]
    }

    /// Get the default parameter environment.
    ///
    /// This is useful for instantiations without any parameter assignment, e.g.
    /// for the top-level module.
    fn default_param_env(&self) -> ParamEnv {
        self.intern_param_env(ParamEnvData::default())
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
}

/// The queries implemented by the compiler.
pub(super) mod queries {
    use super::*;

    salsa::query_group! {
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

            /// Determine the local rib that applies to a node.
            fn local_rib(node_id: NodeId) -> Result<&'a Rib> {
                type LocalRibQuery;
                use fn resolver::local_rib;
            }

            /// Resolve a name upwards through the ribs.
            fn resolve_upwards(name: Name, start_at: NodeId) -> Result<Option<NodeId>> {
                type ResolveUpwardsQuery;
                use fn resolver::resolve_upwards;
            }

        }
    }

    salsa::database_storage! {
        /// The query result storage embedded in the global context.
        pub struct GlobalStorage<'gcx> for GlobalContext<'gcx> {
            impl Context<'gcx> {
                fn hir_of() for HirOfQuery<'gcx>;
                fn param_env() for ParamEnvQuery<'gcx>;
                fn type_of() for TypeOfQuery<'gcx>;
                fn map_to_type() for MapToTypeQuery<'gcx>;
                fn local_rib() for LocalRibQuery<'gcx>;
                fn resolve_upwards() for ResolveUpwardsQuery<'gcx>;
            }
        }
    }
}

pub use self::queries::Context;
