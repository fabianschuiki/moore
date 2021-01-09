// Copyright (c) 2016-2021 Fabian Schuiki

//! Assignment lowering to MIR.

use crate::crate_prelude::*;
use crate::{
    mir::{
        assign::*,
        lower,
        lvalue::{Lvalue, LvalueKind},
        rvalue::{BinaryBitwiseOp, IntBinaryArithOp, Rvalue, RvalueKind, ShiftOp},
    },
    ParamEnv,
};

/// Lower a procedural assign statement.
#[moore_derive::query]
pub(crate) fn mir_assignment_from_procedural<'a>(
    cx: &impl Context<'a>,
    origin: NodeId,
    lhs: NodeId,
    rhs: NodeId,
    env: ParamEnv,
    span: Span, // TODO(fschuiki): Get this from `origin` to not pollute query key
    kind: hir::AssignKind,
) -> &'a mir::Assignment<'a> {
    let lhs_mir_lv = cx.mir_lvalue(lhs, env);
    let rhs_mir = cx.mir_rvalue(rhs, env);

    let value = match kind {
        // `a = b`
        hir::AssignKind::Block(ast::AssignOp::Identity)
        | hir::AssignKind::Nonblock
        | hir::AssignKind::NonblockDelay(_) => Assignment {
            id: origin,
            env,
            span,
            ty: lhs_mir_lv.ty,
            lhs: lhs_mir_lv,
            rhs: rhs_mir,
        },
        // `a (+= -= *= /= %= &= |= ^= <<= >>= <<<= >>>=) b`
        hir::AssignKind::Block(op) => {
            let builder = lower::rvalue::Builder {
                cx,
                span,
                expr: rhs_mir.id,
                env,
            };
            let lhs_mir_rv = cx.mir_rvalue(lhs, env);
            let value = match op {
                ast::AssignOp::Identity => unreachable!(),
                ast::AssignOp::Add => AssignOp::Arith(IntBinaryArithOp::Add),
                ast::AssignOp::Sub => AssignOp::Arith(IntBinaryArithOp::Sub),
                ast::AssignOp::Mul => AssignOp::Arith(IntBinaryArithOp::Mul),
                ast::AssignOp::Div => AssignOp::Arith(IntBinaryArithOp::Div),
                ast::AssignOp::Mod => AssignOp::Arith(IntBinaryArithOp::Mod),
                ast::AssignOp::BitAnd => AssignOp::Bitwise(BinaryBitwiseOp::And),
                ast::AssignOp::BitOr => AssignOp::Bitwise(BinaryBitwiseOp::Or),
                ast::AssignOp::BitXor => AssignOp::Bitwise(BinaryBitwiseOp::Xor),
                ast::AssignOp::LogicShL => AssignOp::Shift(ShiftOp::Left, false),
                ast::AssignOp::LogicShR => AssignOp::Shift(ShiftOp::Right, false),
                ast::AssignOp::ArithShL => AssignOp::Shift(ShiftOp::Left, true),
                ast::AssignOp::ArithShR => AssignOp::Shift(ShiftOp::Right, true),
            };
            let value = match value {
                AssignOp::Arith(op) => lower::rvalue::make_int_binary_arith(
                    &builder,
                    lhs_mir_lv.ty,
                    op,
                    lhs_mir_rv,
                    rhs_mir,
                ),
                AssignOp::Bitwise(op) => lower::rvalue::make_binary_bitwise(
                    &builder,
                    lhs_mir_lv.ty,
                    op,
                    false,
                    lhs_mir_rv,
                    rhs_mir,
                ),
                AssignOp::Shift(op, arith) => lower::rvalue::make_shift(
                    &builder,
                    lhs_mir_lv.ty,
                    op,
                    arith,
                    lhs_mir_rv,
                    rhs_mir,
                ),
            };
            Assignment {
                id: origin,
                env,
                span,
                ty: lhs_mir_lv.ty,
                lhs: lhs_mir_lv,
                rhs: value,
            }
        }
    };

    cx.arena().alloc_mir_assignment(value)
}

enum AssignOp {
    Arith(IntBinaryArithOp),
    Bitwise(BinaryBitwiseOp),
    Shift(ShiftOp, bool),
}

/// Lower a concurrent assign statement.
#[moore_derive::query]
pub(crate) fn mir_assignment_from_concurrent<'a>(
    cx: &impl Context<'a>,
    Ref(assign): Ref<'a, hir::Assign>,
    env: ParamEnv,
) -> &'a mir::Assignment<'a> {
    let lhs_mir = cx.mir_lvalue(assign.lhs, env);
    let rhs_mir = cx.mir_rvalue(assign.rhs, env);
    cx.arena().alloc_mir_assignment(Assignment {
        id: assign.id,
        env,
        span: assign.span,
        ty: lhs_mir.ty,
        lhs: lhs_mir,
        rhs: rhs_mir,
    })
}

/// Simplify an MIR assignment to potentially multiple simple MIR assignments.
///
/// This eliminates assignments to compound `Lvalue` objects, for example
/// concatenations, and replaces them with multiple assignments to each of the
/// individual concatenation fields.
#[moore_derive::query]
pub(crate) fn mir_simplify_assignment<'a>(
    cx: &impl Context<'a>,
    Ref(assign): Ref<'a, mir::Assignment<'a>>,
) -> Vec<&'a mir::Assignment<'a>> {
    let mut v = vec![];
    simplify(cx, assign, assign.lhs, assign.rhs, &mut v);
    v
}

/// Inner function called recursively to simplify assignments.
fn simplify<'a>(
    cx: &impl Context<'a>,
    root: &'a Assignment<'a>,
    lhs: &'a Lvalue<'a>,
    rhs: &'a Rvalue<'a>,
    into: &mut Vec<&'a Assignment<'a>>,
) {
    trace!("Simplifying {:?}", root);
    match lhs.kind {
        LvalueKind::Transmute(value) => simplify(cx, root, value, rhs, into),
        LvalueKind::Concat(ref values) if values.len() == 1 => {
            let mut a = root.clone();
            a.lhs = values[0];
            let a = cx.arena().alloc_mir_assignment(a);
            simplify(cx, a, a.lhs, a.rhs, into);
        }
        LvalueKind::Concat(ref values) => {
            let mut base = 0;
            for value in values.iter().rev() {
                // The value must be of a simple bit vector type, as enforced
                // by the casting logic.
                let sbvt = value.ty.simple_bit_vector(cx, value.span);
                trace!(
                    "- Splitting subassignment to `{}` ({}) at {}",
                    value.span.extract(),
                    sbvt,
                    base
                );

                // Slice the relevant part of the assignment out from the RHS.
                let builder = lower::rvalue::Builder {
                    cx,
                    span: rhs.span,
                    expr: rhs.id,
                    env: rhs.env,
                };
                let base_rv = builder.constant_u32(base as u32);
                let index = builder.build(
                    sbvt.to_unpacked(cx),
                    RvalueKind::Index {
                        value: rhs,
                        base: base_rv,
                        length: sbvt.size,
                    },
                );

                // Formulate a new assignment.
                let mut a = root.clone();
                a.lhs = value;
                a.rhs = index;
                let a = cx.arena().alloc_mir_assignment(a);
                simplify(cx, a, a.lhs, a.rhs, into);

                base += sbvt.size;
            }
        }
        LvalueKind::Index {
            value,
            base,
            length,
        } => match value.kind {
            // If we index into a concatenation, we simply add the (shifted)
            // index to each concatenated value, and emit an individual
            // assignment for each.
            LvalueKind::Concat(ref values) => {
                trace!("Refactoring index into concatenation:\n{:?}", lhs);
                let mut shift = 0;
                for value in values.iter().rev() {
                    // The value must be of a simple bit vector type, as enforced
                    // by the casting logic.
                    let sbvt = value.ty.simple_bit_vector(cx, value.span);

                    // Compute the shifted assignment index.
                    let rbuilder = lower::rvalue::Builder {
                        cx,
                        span: value.span,
                        expr: value.id,
                        env: value.env,
                    };
                    let shift_rv = rbuilder.constant_u32(shift as u32);
                    let base_shifted = rbuilder.build(
                        base.ty,
                        RvalueKind::IntBinaryArith {
                            op: IntBinaryArithOp::Sub,
                            domain: base.ty.domain(),
                            sign: base.ty.sign(),
                            lhs: base,
                            rhs: shift_rv,
                        },
                    );

                    // Add a slice around this concatenated value.
                    let lbuilder = lower::lvalue::Builder {
                        cx,
                        span: value.span,
                        expr: value.id,
                        env: value.env,
                    };
                    let index = lbuilder.build(
                        lhs.ty,
                        LvalueKind::Index {
                            value,
                            base: base_shifted,
                            length,
                        },
                    );

                    // Formulate a new assignment.
                    let mut a = root.clone();
                    a.lhs = index;
                    a.rhs = rhs;
                    let a = cx.arena().alloc_mir_assignment(a);
                    simplify(cx, a, a.lhs, a.rhs, into);

                    shift += sbvt.size;
                }
            }
            _ => {
                into.push(root);
            }
        },
        _ => {
            into.push(root);
        }
    }
}
