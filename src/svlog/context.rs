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
    ty::TypeKind,
};
use llhd;
use std::cell::RefCell;
use std::collections::HashMap;

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
        }
    }

    /// Add root AST nodes to the context for processing.
    ///
    /// Use the `find_global_item` function afterwards to look up the id of
    /// modules that were added.
    pub fn add_root_nodes(&self, ast: &'gcx [ast::Root]) -> Result<()> {
        for root in ast {
            for item in &root.items {
                match *item {
                    ast::Item::Module(ref m) => {
                        let id = self.alloc_id(m.human_span());
                        self.set_ast(id, AstNode::Module(m));
                        self.modules.borrow_mut().insert(m.name, id);
                    }
                    _ => self.unimp(item)?,
                }
            }
        }
        Ok(())
    }

    /// Find a module in the AST.
    pub fn find_module(&self, name: Name) -> Option<NodeId> {
        self.modules.borrow().get(&name).cloned()
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
}

impl Default for GlobalArenas<'_> {
    fn default() -> Self {
        GlobalArenas {
            ids: TypedArena::new(),
            hir: Default::default(),
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

    /// Associate an AST node with a node id.
    fn set_ast(&self, node_id: NodeId, ast: AstNode<'gcx>) {
        self.gcx().ast_map.set(node_id, ast)
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
}

salsa::query_group! {
    /// A collection of compiler queries.
    pub trait Context<'a>: BaseContext<'a> {
        /// Lower an AST node to HIR.
        fn hir_of(node_id: NodeId) -> Result<HirNode<'a>> {
            type HirOf;
            use fn hir::lowering::hir_of;
        }

        /// Determine the type of a node.
        fn type_of(node_id: NodeId) -> Result<Type<'a>> {
            type TypeOf;
            use fn typeck::type_of;
        }
    }
}

salsa::database_storage! {
    /// The query result storage embedded in the global context.
    pub struct GlobalStorage<'gcx> for GlobalContext<'gcx> {
        impl Context<'gcx> {
            fn hir_of() for HirOf<'gcx>;
            fn type_of() for TypeOf<'gcx>;
        }
    }
}
