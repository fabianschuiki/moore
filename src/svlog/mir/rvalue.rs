// Copyright (c) 2016-2019 Fabian Schuiki

//! Rvalue expressions
//!
//! An MIR representation for all expressions that may appear on the right-hand
//! side of an assignment.

use crate::{
    crate_prelude::*,
    mir::lvalue::Lvalue,
    ty::{Domain, Sign, Type},
    ParamEnv,
};
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
    /// A cast from one sign to another. E.g. `logic signed` to
    /// `logic unsigned`.
    CastSign(ty::Sign, &'a Rvalue<'a>),
    /// A cast from a simple bit type to a boolean.
    CastToBool(&'a Rvalue<'a>),
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
    /// Constructor for a struct.
    ConstructStruct(Vec<&'a Rvalue<'a>>),
    /// A constant value.
    Const(value::Value<'a>),
    /// A unary bitwise operator.
    UnaryBitwise {
        op: UnaryBitwiseOp,
        arg: &'a Rvalue<'a>,
    },
    /// A binary bitwise operator.
    BinaryBitwise {
        op: BinaryBitwiseOp,
        lhs: &'a Rvalue<'a>,
        rhs: &'a Rvalue<'a>,
    },
    /// An integral unary arithmetic operator.
    ///
    /// If any bit of the operand is x/z, the entire result is x.
    IntUnaryArith {
        op: IntUnaryArithOp,
        sign: Sign,
        domain: Domain,
        arg: &'a Rvalue<'a>,
    },
    /// An integral binary arithmetic operator.
    ///
    /// If any bit of the operands are x/z, the entire result is x.
    IntBinaryArith {
        op: IntBinaryArithOp,
        sign: Sign,
        domain: Domain,
        lhs: &'a Rvalue<'a>,
        rhs: &'a Rvalue<'a>,
    },
    /// An integral comparison operator.
    ///
    /// If any bit of the operands are x/z, the entire result is x.
    IntComp {
        op: IntCompOp,
        sign: Sign,
        domain: Domain,
        lhs: &'a Rvalue<'a>,
        rhs: &'a Rvalue<'a>,
    },
    /// Concatenate multiple values.
    ///
    /// The values are cast to and treated as packed bit vectors, and the result
    /// is yet another packed bit vector.
    Concat(Vec<&'a Rvalue<'a>>),
    /// Repeat a value multiple times.
    ///
    /// The value is cast to and treated as a packed bit vector, and the result
    /// is yet another packed bit vector.
    Repeat(usize, &'a Rvalue<'a>),
    /// A reference to a variable declaration.
    Var(NodeId),
    /// A reference to a port declaration.
    Port(NodeId),
    /// A bit- or part-select.
    Index {
        value: &'a Rvalue<'a>,
        base: &'a Rvalue<'a>,
        length: usize,
    },
    /// A struct field access.
    Member { value: &'a Rvalue<'a>, field: usize },
    /// The ternary operator.
    Ternary {
        cond: &'a Rvalue<'a>,
        true_value: &'a Rvalue<'a>,
        false_value: &'a Rvalue<'a>,
    },
    /// A shift operation.
    Shift {
        op: ShiftOp,
        arith: bool,
        value: &'a Rvalue<'a>,
        amount: &'a Rvalue<'a>,
    },
    /// A reduction operator.
    Reduction {
        op: BinaryBitwiseOp,
        arg: &'a Rvalue<'a>,
    },
    /// An assignment operator.
    Assignment {
        lvalue: &'a Lvalue<'a>,
        rvalue: &'a Rvalue<'a>,
        /// What value is produced as the assignment's value. This is usually
        /// the rvalue, but may be different (e.g. for the `i++` or `i--`).
        result: &'a Rvalue<'a>,
    },
    /// An error occurred during lowering.
    Error,
}

impl<'a> RvalueKind<'a> {
    /// Check whether the rvalue represents a lowering error tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            RvalueKind::Error => true,
            _ => false,
        }
    }
}

/// The unary bitwise operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum UnaryBitwiseOp {
    Not,
}

/// The binary bitwise operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum BinaryBitwiseOp {
    And,
    Or,
    Xor,
}

/// The integer unary arithmetic operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum IntUnaryArithOp {
    Neg,
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

/// The integer comparison operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum IntCompOp {
    Eq,
    Neq,
    Lt,
    Leq,
    Gt,
    Geq,
}

/// The shift operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum ShiftOp {
    Left,
    Right,
}
