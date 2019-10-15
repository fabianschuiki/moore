// Copyright (c) 2016-2019 Fabian Schuiki

//! Lvalue expressions
//!
//! An MIR representation for all expressions that may appear on the left-hand
//! side of an assignment.

use crate::{crate_prelude::*, mir::Rvalue, ty::Type, ParamEnv};
use std::collections::HashMap;

/// An lvalue expression.
#[derive(Debug, Clone)]
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
    pub ty: Type<'a>,
    /// The expression data.
    pub kind: LvalueKind<'a>,
}

/// The different forms an lvalue expression may take.
#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub enum LvalueKind<'a> {
    /// Destructor for an array.
    DestructArray(HashMap<usize, &'a Lvalue<'a>>),
    /// Destructor for a struct.
    DestructStruct(Vec<&'a Lvalue<'a>>),
    /// A reference to a variable declaration.
    Var(NodeId),
    /// A reference to a port declaration.
    Port(NodeId),
    /// A bit- or part-select.
    Index {
        value: &'a Lvalue<'a>,
        base: &'a Rvalue<'a>,
        length: usize,
    },
    /// A struct field access.
    Member { value: &'a Lvalue<'a>, field: usize },
    /// An error occurred during lowering.
    Error,
}
