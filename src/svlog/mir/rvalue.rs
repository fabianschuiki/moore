// Copyright (c) 2016-2019 Fabian Schuiki

//! Rvalue expressions
//!
//! An MIR representation for all expressions that may appear on the right-hand
//! side of an assignment.

use crate::{crate_prelude::*, ty::Type, ParamEnv};
use std::collections::HashMap;

/// An rvalue expression.
#[derive(Debug, Clone)]
pub struct Rvalue<'a> {
    /// A unique id.
    pub id: NodeId,
    /// The expression node which spawned this rvalue.
    pub origin: NodeId,
    /// The environment within which the rvalue lives.
    pub env: ParamEnv,
    /// The span in the source file where the rvalue originates from.
    pub span: Span,
    /// The type of the expression.
    pub ty: Type<'a>,
    /// The expression data.
    pub kind: RvalueKind<'a>,
}

/// The different forms an rvalue expression may take.
#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub enum RvalueKind<'a> {
    /// A cast from a four-valued type to a two-valued type, or vice versa.
    /// E.g. `integer` to `int`, or `int` to `integer`.
    CastValueDomain {
        from: ty::Domain,
        to: ty::Domain,
        value: &'a Rvalue<'a>,
    },
    /// A cast from a single-element vector type to an atom type.
    /// E.g. `bit [0:0]` to `bit`.
    CastVectorToAtom {
        domain: ty::Domain,
        value: &'a Rvalue<'a>,
    },
    /// A cast from an atom type to a single-element vector type.
    /// E.g. `bit` to `bit [0:0]`.
    CastAtomToVector {
        domain: ty::Domain,
        value: &'a Rvalue<'a>,
    },
    /// Shrink the width of a vector type. E.g. `bit [31:0]` to `bit [7:0]`.
    Truncate(usize, &'a Rvalue<'a>),
    /// Increase the width of a vector by zero extension. E.g. `bit [7:0]` to
    /// `bit [31:0]`.
    ZeroExtend(usize, &'a Rvalue<'a>),
    /// Increase the width of a vector by sign extension. E.g. `bit signed
    /// [7:0]` to `bit signed [31:0]`.
    SignExtend(usize, &'a Rvalue<'a>),
    /// Constructor for an array.
    ConstructArray(HashMap<usize, &'a Rvalue<'a>>),
    /// A constant value.
    Const(value::Value<'a>),
    /// An integral binary arithmetic operator.
    ///
    /// If any bit of the operands are x/z, the entire result is x.
    IntBinaryArith {
        op: IntBinaryArithOp,
        width: usize,
        lhs: &'a Rvalue<'a>,
        rhs: &'a Rvalue<'a>,
        // TODO(fschuiki): Add sign of the operation.
    },
    /// An error occurred during lowering.
    Error,
}

/// The integer binary arithmetic operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum IntBinaryArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
}
