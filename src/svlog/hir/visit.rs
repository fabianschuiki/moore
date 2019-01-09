// Copyright (c) 2016-2019 Fabian Schuiki

//! An implementation of the visitor pattern for the HIR.
//!
//! This module defines the [`Visitor`] trait that allows the HIR tree graph to
//! be visited.

use super::{nodes::*, HirNode};
use crate::{common::NodeId, Context};

/// A visitor of the HIR.
pub trait Visitor<'a>: Sized {
    /// The type of context that this visitor uses.
    type Context: Context<'a>;

    /// Get the context to be used to resolve queries.
    fn context(&self) -> &Self::Context;

    fn visit_node_with_id(&mut self, node_id: NodeId, lvalue: bool) {
        match self.context().hir_of(node_id) {
            Ok(x) => self.visit_node(x, lvalue),
            Err(()) => (),
        }
    }

    fn visit_node(&mut self, node: HirNode<'a>, lvalue: bool) {
        match node {
            HirNode::Proc(x) => self.visit_proc(x),
            HirNode::Stmt(x) => self.visit_stmt(x),
            HirNode::Expr(x) => self.visit_expr(x, lvalue),
            _ => (),
        }
    }

    fn visit_proc(&mut self, prok: &'a Proc) {
        walk_proc(self, prok)
    }

    fn visit_stmt(&mut self, stmt: &'a Stmt) {
        walk_stmt(self, stmt)
    }

    fn visit_expr(&mut self, expr: &'a Expr, lvalue: bool) {
        walk_expr(self, expr, lvalue);
    }
}

/// Walk the contents of a procedure.
pub fn walk_proc<'a>(visitor: &mut impl Visitor<'a>, prok: &'a Proc) {
    visitor.visit_node_with_id(prok.stmt, false);
}

/// Walk the contents of a statement.
pub fn walk_stmt<'a>(visitor: &mut impl Visitor<'a>, stmt: &'a Stmt) {
    #[allow(unreachable_patterns)]
    match stmt.kind {
        StmtKind::Null => (),
        StmtKind::Block(ref stmts) => {
            for &id in stmts {
                visitor.visit_node_with_id(id, false);
            }
        }
        StmtKind::Assign { lhs, rhs, .. } => {
            visitor.visit_node_with_id(lhs, true);
            visitor.visit_node_with_id(rhs, false);
        }
        _ => (),
    }
}

/// Walk the contents of an expression.
pub fn walk_expr<'a>(_visitor: &mut impl Visitor<'a>, expr: &'a Expr, _lvalue: bool) {
    match expr.kind {
        _ => (),
    }
}
