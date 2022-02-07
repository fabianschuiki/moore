// Copyright (c) 2016-2021 Fabian Schuiki

//! Rvalue expressions
//!
//! An MIR representation for all expressions that may appear on the right-hand
//! side of an assignment.

use crate::crate_prelude::*;
use crate::{
    mir::{
        lvalue::Lvalue,
        print::{Context, Print},
        visit::{AcceptVisitor, Visitor, WalkVisitor},
    },
    ty::{Domain, Sign, UnpackedType},
    ParamEnv,
};
use num::BigRational;
use std::collections::HashMap;
use std::fmt::Write;

/// An rvalue expression.
#[moore_derive::visit_without_foreach]
#[derive(Clone, Eq, PartialEq)]
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

impl<'a> std::fmt::Debug for Rvalue<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.print(f)
    }
}

impl<'a> Print for Rvalue<'a> {
    fn print_context(
        &self,
        outer: &mut impl Write,
        inner: &mut impl Write,
        ctx: &mut Context,
    ) -> std::fmt::Result {
        write!(inner, "Rvalue ")?;
        match self.kind {
            RvalueKind::CastValueDomain { value, .. } => {
                write!(inner, "CastValueDomain({})", ctx.print(outer, value))?
            }
            RvalueKind::Transmute(v) => write!(inner, "Transmute({})", ctx.print(outer, v))?,
            RvalueKind::CastSign(sign, arg) => {
                write!(inner, "CastSign({}, {})", sign, ctx.print(outer, arg))?
            }
            RvalueKind::CastToBool(arg) => write!(inner, "CastToBool({})", ctx.print(outer, arg))?,
            RvalueKind::ApplyTimescale(arg, ref scale) => write!(
                inner,
                "ApplyTimescale({}, {})",
                ctx.print(outer, arg),
                scale
            )?,
            RvalueKind::Truncate(size, arg) => {
                write!(inner, "Truncate({}, {})", size, ctx.print(outer, arg))?
            }
            RvalueKind::ZeroExtend(size, arg) => {
                write!(inner, "ZeroExtend({}, {})", size, ctx.print(outer, arg))?
            }
            RvalueKind::SignExtend(size, arg) => {
                write!(inner, "SignExtend({}, {})", size, ctx.print(outer, arg))?
            }
            RvalueKind::ConstructArray(ref args) => write!(
                inner,
                "ConstructArray({})",
                ctx.print_comma_separated(outer, args.iter().map(|(_idx, v)| v)),
            )?,
            RvalueKind::ConstructStruct(ref args) => write!(
                inner,
                "ConstructStruct({})",
                ctx.print_comma_separated(outer, args),
            )?,
            RvalueKind::Const(arg) => write!(inner, "{}", arg)?,
            RvalueKind::UnaryBitwise { op, arg } => {
                write!(inner, "UnaryBitwise {:?} {}", op, ctx.print(outer, arg))?
            }
            RvalueKind::BinaryBitwise { op, lhs, rhs } => write!(
                inner,
                "BinaryBitwise {} {:?} {}",
                ctx.print(outer, lhs),
                op,
                ctx.print(outer, rhs)
            )?,
            RvalueKind::IntUnaryArith {
                op,
                sign,
                domain,
                arg,
            } => write!(
                inner,
                "IntUnaryArith {:?} {} ({:?}, {:?})",
                op,
                ctx.print(outer, arg),
                sign,
                domain
            )?,
            RvalueKind::IntBinaryArith {
                op,
                sign,
                domain,
                lhs,
                rhs,
            } => write!(
                inner,
                "IntBinaryArith {} {:?} {} ({:?}, {:?})",
                ctx.print(outer, lhs),
                op,
                ctx.print(outer, rhs),
                sign,
                domain
            )?,
            RvalueKind::IntComp {
                op,
                sign,
                domain,
                lhs,
                rhs,
            } => write!(
                inner,
                "IntComp {} {:?} {} ({:?}, {:?})",
                ctx.print(outer, lhs),
                op,
                ctx.print(outer, rhs),
                sign,
                domain
            )?,
            RvalueKind::Concat(ref args) => {
                write!(inner, "Concat({})", ctx.print_comma_separated(outer, args))?
            }
            RvalueKind::Repeat(num, arg) => {
                write!(inner, "Repeat({} x {})", num, ctx.print(outer, arg))?
            }
            RvalueKind::Var(arg) => write!(inner, "Var({:?})", arg)?,
            RvalueKind::Port(arg) => write!(inner, "Port({:?})", arg)?,
            RvalueKind::Arg(arg) => write!(inner, "Arg({:?})", arg)?,
            RvalueKind::Intf(arg) => write!(inner, "Intf({:?})", arg)?,
            RvalueKind::IntfSignal(arg, sig) => {
                write!(inner, "IntfSignal({}, {:?})", ctx.print(outer, arg), sig)?
            }
            RvalueKind::Index {
                value,
                base,
                length,
            } => {
                if length == 0 {
                    write!(
                        inner,
                        "{}[{}]",
                        ctx.print(outer, value),
                        ctx.print(outer, base)
                    )?
                } else {
                    write!(
                        inner,
                        "{}[{}+:{}]",
                        ctx.print(outer, value),
                        ctx.print(outer, base),
                        length,
                    )?
                }
            }
            RvalueKind::Member { value, field } => {
                write!(inner, "{}.{}", ctx.print(outer, value), field)?
            }
            RvalueKind::Ternary {
                cond,
                true_value,
                false_value,
            } => write!(
                inner,
                "{} ? {} : {}",
                ctx.print(outer, cond),
                ctx.print(outer, true_value),
                ctx.print(outer, false_value)
            )?,
            RvalueKind::Shift {
                op,
                arith,
                value,
                amount,
            } => write!(
                inner,
                "Shift {:?} {} {} by {}",
                op,
                if arith { "arith" } else { "logic" },
                ctx.print(outer, value),
                ctx.print(outer, amount)
            )?,
            RvalueKind::Reduction { op, arg } => {
                write!(inner, "Reduce({:?}, {})", op, ctx.print(outer, arg))?
            }
            RvalueKind::Assignment {
                lvalue,
                rvalue,
                result,
            } => write!(
                inner,
                "{}, {{ {} = {} }}",
                ctx.print(outer, result),
                ctx.print(outer, lvalue),
                ctx.print(outer, rvalue)
            )?,
            RvalueKind::PackString(arg) => write!(inner, "PackString({})", ctx.print(outer, arg))?,
            RvalueKind::UnpackString(arg) => {
                write!(inner, "UnpackString({})", ctx.print(outer, arg))?
            }
            RvalueKind::StringComp { op, lhs, rhs } => write!(
                inner,
                "StringComp {} {:?} {}",
                ctx.print(outer, lhs),
                op,
                ctx.print(outer, rhs)
            )?,
            RvalueKind::Call { target, ref args } => {
                write!(
                    inner,
                    "Call {} ({})",
                    target.prototype.name,
                    ctx.print_comma_separated(outer, args),
                )?;
            }
            RvalueKind::Error => write!(inner, "<error>")?,
        }
        write!(inner, " : {}", self.ty)?;
        Ok(())
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
    /// is yet another packed bit vector. The lowest index corresponds to the
    /// left-most item in the concatenation, which is at the MSB end of the
    /// final packed bit vector.
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
    /// A reference to a subroutine argument.
    Arg(NodeId),
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
    /// Convert an integer to a time value by applying the currently active timescale.
    ApplyTimescale(&'a Rvalue<'a>, BigRational),
    /// A function or task call.
    Call {
        /// The called function.
        #[dont_visit]
        target: &'a ast::SubroutineDecl<'a>,
        /// The call arguments.
        args: Vec<CallArg<'a>>,
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
            | RvalueKind::UnpackString(value)
            | RvalueKind::ApplyTimescale(value, _) => value.is_const(),
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
            RvalueKind::Arg(_) => false,
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
            // TODO(fschuiki): This is wrong; function calls *may* be constant
            // under certain circumstances.
            RvalueKind::Call { .. } => false,
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

/// A call input argument.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallInput<'a> {
    /// The argument is passed by value.
    ByValue(&'a Rvalue<'a>),
    /// The argument is passed by reference.
    ByRef(&'a Lvalue<'a>),
}

impl<'a> Print for CallInput<'a> {
    fn print_context(
        &self,
        outer: &mut impl Write,
        inner: &mut impl Write,
        ctx: &mut Context,
    ) -> std::fmt::Result {
        match self {
            Self::ByValue(x) => x.print_context(outer, inner, ctx),
            Self::ByRef(x) => x.print_context(outer, inner, ctx),
        }
    }
}

/// A call argument.
#[moore_derive::visit_without_foreach]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallArg<'a> {
    /// An input argument. Passed to the function by value.
    Input(&'a Rvalue<'a>),
    /// An output argument. Passed as a temporary variable to the function. The
    /// after the function returns, a post-assignment in the `RvalueKind::Call`
    /// is responsible for transfering the value from the temporary variable to
    /// the actual `Lvalue` listed here, if any. This ensures signals passed as
    /// output arguments get a proper blocking assignment.
    Output(&'a UnpackedType<'a>, Option<&'a Lvalue<'a>>),
    /// An inout argument. Same as `CallArg::Output`, but the variable is
    /// initialized to the provided value.
    Inout(&'a Rvalue<'a>, Option<&'a Lvalue<'a>>),
    /// A by-ref argument. Passed into the function as-is.
    Ref(&'a Lvalue<'a>),
}

impl<'a> Print for CallArg<'a> {
    fn print_context(
        &self,
        outer: &mut impl Write,
        inner: &mut impl Write,
        ctx: &mut Context,
    ) -> std::fmt::Result {
        match self {
            Self::Input(x) => {
                write!(inner, "in:")?;
                x.print_context(outer, inner, ctx)
            }
            Self::Output(_, x) => {
                write!(inner, "out:")?;
                x.print_context(outer, inner, ctx)
            }
            Self::Inout(x, y) => {
                write!(inner, "in:")?;
                x.print_context(outer, inner, ctx)?;
                write!(inner, "/")?;
                y.print_context(outer, inner, ctx)
            }
            Self::Ref(x) => {
                write!(inner, "ref:")?;
                x.print_context(outer, inner, ctx)
            }
        }
    }
}
