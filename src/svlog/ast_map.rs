// Copyright (c) 2016-2019 Fabian Schuiki

//! A mapping from node IDs to AST nodes.

use ast;
use common::NodeId;
use std::cell::RefCell;
use std::collections::HashMap;

#[derive(Default)]
pub struct AstMap<'ast> {
    map: RefCell<HashMap<NodeId, AstNode<'ast>>>,
}

impl<'ast> AstMap<'ast> {
    pub fn set(&self, id: NodeId, node: impl Into<AstNode<'ast>>) {
        let node = node.into();
        if self.map.borrow_mut().insert(id, node).is_some() {
            panic!("An AST node with ID {} already exists in the map", id);
        }
    }
}

pub enum AstNode<'ast> {
    Module(&'ast ast::ModDecl),
}
