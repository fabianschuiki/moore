// Copyright (c) 2016-2020 Fabian Schuiki

//! Assignments
//!
//! An MIR representation for assignments of an `Rvalue` to and `Lvalue`. This
//! node allows for complex assignments to concatenations to be transformed into
//! multiple simpler assignments.

use crate::crate_prelude::*;
use crate::{
    mir::{
        lvalue::Lvalue,
        rvalue::Rvalue,
        visit::{AcceptVisitor, Visitor, WalkVisitor},
    },
    ty::UnpackedType,
    ParamEnv,
};

/// An assignment of an `Rvalue` to an `Lvalue`.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Assignment<'a> {
    /// The expression or statement which spawned this assignment.
    pub id: NodeId,
    /// The environment within which the assignment lives.
    pub env: ParamEnv,
    /// The span in the source file where the assignment originates from.
    pub span: Span,
    /// The type of the assignment.
    pub ty: &'a UnpackedType<'a>,
    /// The left-hand side.
    pub lhs: &'a Lvalue<'a>,
    /// The right-hand side.
    pub rhs: &'a Rvalue<'a>,
}

impl<'a> Assignment<'a> {
    /// Check whether the assignment represents a lowering error tombstone.
    pub fn is_error(&self) -> bool {
        self.lhs.is_error() || self.rhs.is_error()
    }
}
