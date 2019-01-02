// Copyright (c) 2016-2019 Fabian Schuiki

//! The central data structure of the compiler.
//!
//! The two main data structures defined in this module [`Context`] and
//! [`GlobalContext`] are the backbone of compilation. `Context` is a light
//! pointer passed to each and every function. It contains a reference to the
//! `GlobalContext` which acts as a backing storage for all data generated
//! during the compilation and holds pointers to the input AST.
//!
//! # Example
//!
//! ```
//! # extern crate moore_common as common;
//! # extern crate moore_svlog as svlog;
//! # use common::Session;
//! # use svlog::{Context, GlobalContext};
//! let sess = Session::new();
//! let gcx = GlobalContext::new(&sess);
//! let cx = Context::new(&gcx);
//! ```

use crate::ast;
use crate::ast_map::{AstMap, AstNode};
use crate::codegen;
use crate::common::arenas::Alloc;
use crate::common::arenas::TypedArena;
use crate::common::Session;
use crate::crate_prelude::*;
use crate::hir::{self, HirNode};
use llhd;
use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;

/// The central data structure of the compiler. It stores references to various
/// arenas and tables that store the results of the various computations that
/// have been performed.
#[derive(Copy, Clone)]
pub struct Context<'gcx> {
    gcx: &'gcx GlobalContext<'gcx>,
}

// Allow `Context` to be implicitly dereferenced as `GlobalContext`.
impl<'gcx> Deref for Context<'gcx> {
    type Target = &'gcx GlobalContext<'gcx>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.gcx
    }
}

impl<'gcx> Context<'gcx> {
    pub fn new(gcx: &'gcx GlobalContext<'gcx>) -> Self {
        Context { gcx }
    }

    /// Emit an internal compiler error that a node is not implemented.
    pub fn unimp<T, R>(self, node: &T) -> Result<R>
    where
        T: HasSpan + HasDesc,
    {
        self.emit(
            DiagBuilder2::bug(format!("{} not implemented", node.desc_full()))
                .span(node.human_span()),
        );
        Err(())
    }

    pub fn add_root_nodes(self, ast: &'gcx [ast::Root]) -> Result<()> {
        for root in ast {
            for item in &root.items {
                match *item {
                    ast::Item::Module(ref m) => {
                        let id = self.alloc_id(m.human_span());
                        self.set_ast(id, AstNode::Module(m));
                        self.register_global_item(m.name, GlobalItem::Module(id));
                    }
                    _ => self.unimp(item)?,
                }
            }
        }
        Ok(())
    }

    fn register_global_item(self, name: Name, item: GlobalItem) {
        self.global_items.borrow_mut().insert(name, item);
    }

    pub fn find_global_item(self, name: Name) -> Option<GlobalItem> {
        self.global_items.borrow().get(&name).cloned()
    }

    /// Allocate a new node id.
    ///
    /// The provided span is used primarily for diagnostic messages and is
    /// supposed to easily identify the node to the user in case of an error.
    pub fn alloc_id(self, span: Span) -> NodeId {
        let id = NodeId::alloc();
        self.node_id_to_span.borrow_mut().insert(id, span);
        id
    }

    /// Associate an AST ndoe with a node id.
    pub fn set_ast(self, node_id: NodeId, ast: AstNode<'gcx>) {
        self.ast_map.set(node_id, ast)
    }

    /// Obtain the AST node associated with a node id.
    pub fn ast_of(self, node_id: NodeId) -> Result<AstNode<'gcx>> {
        match self.ast_map.get(node_id) {
            Some(node) => Ok(node),
            None => {
                let span = self.node_id_to_span.borrow()[&node_id];
                self.emit(
                    DiagBuilder2::bug(format!("no ast node for `{}` in the map", span.extract()))
                        .span(span),
                );
                Err(())
            }
        }
    }

    /// Lower a an AST node to HIR.
    pub fn hir_of(self, node_id: NodeId) -> Result<HirNode<'gcx>> {
        hir::lowering::hir_of(self, node_id)
    }

    /// Generate code for a node.
    pub fn generate_code(self, node_id: NodeId) -> Result<llhd::Module> {
        codegen::generate_code(self, node_id)
    }
}

/// The owner of all data generated during compilation.
pub struct GlobalContext<'gcx> {
    /// The global compiler session.
    pub sess: &'gcx Session,
    /// The mapping of node IDs to abstract syntax tree nodes.
    ast_map: AstMap<'gcx>,
    /// The items visible in the global scope.
    global_items: RefCell<HashMap<Name, GlobalItem>>,
    /// A mapping from node ids to spans for diagnostics.
    node_id_to_span: RefCell<HashMap<NodeId, Span>>,
    /// The arenas that own all references.
    pub arenas: GlobalArenas<'gcx>,
}

impl<'gcx> GlobalContext<'gcx> {
    /// Create a new global context.
    pub fn new(sess: &'gcx Session) -> Self {
        GlobalContext {
            sess,
            ast_map: Default::default(),
            global_items: Default::default(),
            node_id_to_span: Default::default(),
            arenas: Default::default(),
        }
    }
}

impl DiagEmitter for GlobalContext<'_> {
    fn emit(&self, diag: DiagBuilder2) {
        self.sess.emit(diag)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum GlobalItem {
    Module(NodeId),
}

impl Into<NodeId> for GlobalItem {
    fn into(self) -> NodeId {
        match self {
            GlobalItem::Module(x) => x,
        }
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
