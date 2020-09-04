// Copyright (c) 2016-2020 Fabian Schuiki

//! Rvalue expressions
//!
//! An MIR representation for all expressions that may appear on the right-hand
//! side of an assignment.

use crate::crate_prelude::*;
use crate::{
    mir::{
        lvalue::Lvalue,
        visit::{AcceptVisitor, Visitor, WalkVisitor},
    },
    ty::{Domain, Sign, UnpackedType},
    ParamEnv,
};
use std::collections::HashMap;

/// An rvalue expression.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Eq, PartialEq)]
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
    pub ty: &'a UnpackedType<'a>,
    /// The expression data.
    pub kind: RvalueKind<'a>,
    /// Whether this expression has a constant value.
    pub konst: bool,
}

impl<'a> Rvalue<'a> {
    /// Check whether the rvalue represents a lowering error tombstone.
    pub fn is_error(&self) -> bool {
        self.ty.is_error() || self.kind.is_error()
    }

    /// Check whether the rvalue is a constant.
    pub fn is_const(&self) -> bool {
        self.konst
    }

    /// Get the `Intf` nested within `Index`, if one exists.
    pub fn get_intf(&self) -> Option<NodeId> {
        match self.kind {
            mir::RvalueKind::Index { value, .. } => value.get_intf(),
            mir::RvalueKind::Intf(intf) => Some(intf),
            _ => None,
        }
    }
}

impl<'a> std::ops::Deref for Rvalue<'a> {
    type Target = RvalueKind<'a>;

    fn deref(&self) -> &RvalueKind<'a> {
        &self.kind
    }
}

/// The different forms an rvalue expression may take.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum RvalueKind<'a> {
    /// A cast from a four-valued type to a two-valued type, or vice versa.
    /// E.g. `integer` to `int`, or `int` to `integer`.
    CastValueDomain {
        from: ty::Domain,
        to: ty::Domain,
        value: &'a Rvalue<'a>,
    },
    /// A type cast which does not incur any operation. For example, going from
    /// `bit [31:0]` to `int`, or vice versa.
    Transmute(&'a Rvalue<'a>),
    /// A cast from one sign to another. E.g. `logic signed` to
    /// `logic unsigned`.
    // TODO: Add SBVT
    CastSign(ty::Sign, &'a Rvalue<'a>),
    /// A cast from a simple bit type to a boolean.
    // TODO: Add SBVT
    CastToBool(&'a Rvalue<'a>),
    /// Shrink the width of a vector type. E.g. `bit [31:0]` to `bit [7:0]`.
    // TODO: Add SBVT
    Truncate(usize, &'a Rvalue<'a>),
    /// Increase the width of a vector by zero extension. E.g. `bit [7:0]` to
    /// `bit [31:0]`.
    // TODO: Add SBVT
    ZeroExtend(usize, &'a Rvalue<'a>),
    /// Increase the width of a vector by sign extension. E.g. `bit signed
    /// [7:0]` to `bit signed [31:0]`.
    // TODO: Add SBVT
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
        // TODO: Add SBVT
        arg: &'a Rvalue<'a>,
    },
    /// A binary bitwise operator.
    BinaryBitwise {
        op: BinaryBitwiseOp,
        // TODO: Add SBVT
        lhs: &'a Rvalue<'a>,
        rhs: &'a Rvalue<'a>,
    },
    /// An integral unary arithmetic operator.
    ///
    /// If any bit of the operand is x/z, the entire result is x.
    IntUnaryArith {
        op: IntUnaryArithOp,
        // TODO: Add SBVT
        sign: Sign,
        domain: Domain,
        arg: &'a Rvalue<'a>,
    },
    /// An integral binary arithmetic operator.
    ///
    /// If any bit of the operands are x/z, the entire result is x.
    IntBinaryArith {
        op: IntBinaryArithOp,
        // TODO: Add SBVT
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
        // TODO: Add SBVT
        sign: Sign,
        domain: Domain,
        lhs: &'a Rvalue<'a>,
        rhs: &'a Rvalue<'a>,
    },
    /// Concatenate multiple values.
    ///
    /// The values are cast to and treated as packed bit vectors, and the result
    /// is yet another packed bit vector.
    // TODO: Add SBVT
    Concat(Vec<&'a Rvalue<'a>>),
    /// Repeat a value multiple times.
    ///
    /// The value is cast to and treated as a packed bit vector, and the result
    /// is yet another packed bit vector.
    // TODO: Add SBVT
    Repeat(usize, &'a Rvalue<'a>),
    /// A reference to a variable declaration.
    Var(NodeId),
    /// A reference to a port declaration.
    Port(NodeId),
    /// A reference to an interface.
    Intf(NodeId),
    /// A reference to a locally instantiated interface signal.
    IntfSignal(&'a Rvalue<'a>, NodeId),
    /// A bit- or part-select.
    Index {
        value: &'a Rvalue<'a>,
        base: &'a Rvalue<'a>,
        /// Length of the selection. Bit-select if zero.
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
        // TODO: Add SBVT
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
    /// Pack a string value into a fixed-size packed bit vector.
    PackString(&'a Rvalue<'a>),
    /// Unpack a string value from a fixed-size packed bit vector.
    UnpackString(&'a Rvalue<'a>),
    /// A string comparison operator.
    StringComp {
        op: StringCompOp,
        lhs: &'a Rvalue<'a>,
        rhs: &'a Rvalue<'a>,
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

    /// Check whether this rvalue is a constant.
    pub fn is_const(&self) -> bool {
        match self {
            RvalueKind::CastValueDomain { value, .. }
            | RvalueKind::Transmute(value)
            | RvalueKind::CastSign(_, value)
            | RvalueKind::CastToBool(value)
            | RvalueKind::Truncate(_, value)
            | RvalueKind::ZeroExtend(_, value)
            | RvalueKind::SignExtend(_, value)
            | RvalueKind::Repeat(_, value)
            | RvalueKind::Member { value, .. }
            | RvalueKind::PackString(value)
            | RvalueKind::UnpackString(value) => value.is_const(),
            RvalueKind::ConstructArray(values) => values.values().all(|v| v.is_const()),
            RvalueKind::ConstructStruct(values) => values.iter().all(|v| v.is_const()),
            RvalueKind::Const(_) => true,
            RvalueKind::UnaryBitwise { arg, .. }
            | RvalueKind::IntUnaryArith { arg, .. }
            | RvalueKind::Reduction { arg, .. } => arg.is_const(),
            RvalueKind::BinaryBitwise { lhs, rhs, .. }
            | RvalueKind::IntBinaryArith { lhs, rhs, .. }
            | RvalueKind::IntComp { lhs, rhs, .. }
            | RvalueKind::StringComp { lhs, rhs, .. } => lhs.is_const() && rhs.is_const(),
            RvalueKind::Concat(values) => values.iter().all(|v| v.is_const()),
            RvalueKind::Var(_) => false,
            RvalueKind::Port(_) => false,
            RvalueKind::Intf(_) => false,
            RvalueKind::IntfSignal(..) => false,
            RvalueKind::Index { .. } => false, // TODO(fschuiki): reactivate once impl
            // RvalueKind::Index { value, base, .. } => value.is_const() && base.is_const(),
            RvalueKind::Ternary {
                cond,
                true_value,
                false_value,
            } => cond.is_const() && true_value.is_const() && false_value.is_const(),
            RvalueKind::Shift { value, amount, .. } => value.is_const() && amount.is_const(),
            RvalueKind::Assignment { .. } => false,
            RvalueKind::Error => true,
        }
    }
}

/// The unary bitwise operators.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum UnaryBitwiseOp {
    Not,
}

/// The binary bitwise operators.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum BinaryBitwiseOp {
    And,
    Or,
    Xor,
}

/// The integer unary arithmetic operators.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum IntUnaryArithOp {
    Neg,
}

/// The integer binary arithmetic operators.
#[moore_derive::visit_without_foreach]
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
#[moore_derive::visit_without_foreach]
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

/// The string comparison operators.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum StringCompOp {
    Eq,
    Neq,
}

/// The shift operators.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum ShiftOp {
    Left,
    Right,
}
