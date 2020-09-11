// Copyright (c) 2016-2020 Fabian Schuiki

//! Lvalue expressions
//!
//! An MIR representation for all expressions that may appear on the left-hand
//! side of an assignment.

use crate::crate_prelude::*;
use crate::{
    mir::{
        rvalue::Rvalue,
        visit::{AcceptVisitor, Visitor, WalkVisitor},
    },
    ty::UnpackedType,
    ParamEnv,
};
use std::collections::HashMap;

/// An lvalue expression.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Lvalue<'a> {
    /// A unique id.
    pub id: NodeId,
    /// The expression node which spawned this lvalue.
    pub origin: NodeId,
    /// The environment within which the lvalue lives.
    pub env: ParamEnv,
    /// The span in the source file where the lvalue originates from.
    pub span: Span,
    /// The type of the expression.
    pub ty: &'a UnpackedType<'a>,
    /// The expression data.
    pub kind: LvalueKind<'a>,
}

impl<'a> Lvalue<'a> {
    /// Check whether the lvalue represents a lowering error tombstone.
    pub fn is_error(&self) -> bool {
        self.ty.is_error() || self.kind.is_error()
    }

    /// Get the `Intf` nested within `Index`, if one exists.
    pub fn get_intf(&self) -> Option<NodeId> {
        match self.kind {
            mir::LvalueKind::Index { value, .. } => value.get_intf(),
            mir::LvalueKind::Intf(intf) => Some(intf),
            _ => None,
        }
    }
}

/// The different forms an lvalue expression may take.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum LvalueKind<'a> {
    /// Destructor for an array.
    DestructArray(HashMap<usize, &'a Lvalue<'a>>),
    /// Destructor for a struct.
    DestructStruct(Vec<&'a Lvalue<'a>>),
    /// A reference to a genvar declaration.
    Genvar(NodeId),
    /// A reference to a variable declaration.
    Var(NodeId),
    /// A reference to a port declaration.
    Port(NodeId),
    /// A reference to an interface.
    Intf(NodeId),
    /// A reference to an interface's signal.
    IntfSignal(&'a Lvalue<'a>, NodeId),
    /// A bit- or part-select.
    Index {
        value: &'a Lvalue<'a>,
        base: &'a Rvalue<'a>,
        length: usize,
    },
    /// A struct field access.
    Member { value: &'a Lvalue<'a>, field: usize },
    /// Concatenate multiple values.
    ///
    /// The values are cast to and treated as packed bit vectors, and the result
    /// is yet another packed bit vector.
    Concat(Vec<&'a Lvalue<'a>>),
    /// Repeat a value multiple times.
    ///
    /// The value is cast to and treated as a packed bit vector, and the result
    /// is yet another packed bit vector.
    Repeat(usize, &'a Lvalue<'a>),
    /// An error occurred during lowering.
    Error,
}

impl<'a> LvalueKind<'a> {
    /// Check whether the lvalue represents a lowering error tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            LvalueKind::Error => true,
            _ => false,
        }
    }
}
