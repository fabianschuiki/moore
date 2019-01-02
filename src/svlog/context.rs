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
use crate::common::errors::*;
use crate::common::name::Name;
use crate::common::score::Result;
use crate::common::util::{HasDesc, HasSpan};
use crate::common::NodeId;
use crate::common::Session;
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
                        let id = NodeId::alloc();
                        self.ast_map.set(id, AstNode::Module(m));
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

    /// Obtain the AST node associated with a node id.
    pub fn ast_of(self, node_id: NodeId) -> Result<AstNode<'gcx>> {
        match self.ast_map.get(node_id) {
            Some(node) => Ok(node),
            None => {
                self.emit(DiagBuilder2::bug(format!(
                    "no ast node for id {} in the map",
                    node_id
                )));
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
#[derive(Default)]
pub struct GlobalArenas<'t> {
    hir: hir::Arena<'t>,
}

impl<'t> GlobalArenas<'t> {
    /// Allocate an HIR node into the global context.
    pub fn alloc_hir<T>(&'t self, hir: T) -> &T
    where
        hir::Arena<'t>: Alloc<'t, 't, T>,
        T: 't,
    {
        self.hir.alloc(hir)
    }
}
