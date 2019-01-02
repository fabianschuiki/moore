// Copyright (c) 2016-2019 Fabian Schuiki

//! A mapping from node IDs to AST nodes.

use ast;
use common::source::Span;
use common::util::{HasDesc, HasSpan};
use common::NodeId;
use std::cell::RefCell;
use std::collections::HashMap;

#[derive(Default)]
pub struct AstMap<'ast> {
    map: RefCell<HashMap<NodeId, AstNode<'ast>>>,
}

impl<'ast> AstMap<'ast> {
    /// Insert an AST node into the map.
    pub fn set(&self, id: NodeId, node: impl Into<AstNode<'ast>>) {
        let node = node.into();
        if self.map.borrow_mut().insert(id, node).is_some() {
            panic!("An AST node with ID {} already exists in the map", id);
        }
    }

    /// Retrieve an AST node from the map.
    pub fn get(&self, id: NodeId) -> Option<AstNode<'ast>> {
        self.map.borrow().get(&id).cloned()
    }
}

/// A reference to an AST node.
///
/// This enum essentially provides a wrapper around typed references to AST
/// nodes. It allows code to obtain a generic reference to an AST node and then
/// match on the actual type that was provided.
#[derive(Clone, Copy, Debug)]
pub enum AstNode<'ast> {
    Module(&'ast ast::ModDecl),
}

impl<'ast> HasSpan for AstNode<'ast> {
    fn span(&self) -> Span {
        match *self {
            AstNode::Module(m) => m.span(),
        }
    }

    fn human_span(&self) -> Span {
        match *self {
            AstNode::Module(m) => m.human_span(),
        }
    }
}

impl<'ast> HasDesc for AstNode<'ast> {
    fn desc(&self) -> &'static str {
        match *self {
            AstNode::Module(m) => m.desc(),
        }
    }

    fn desc_full(&self) -> String {
        match *self {
            AstNode::Module(m) => m.desc_full(),
        }
    }
}
