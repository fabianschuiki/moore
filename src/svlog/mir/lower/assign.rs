// Copyright (c) 2016-2020 Fabian Schuiki

//! Assignment lowering to MIR.

use crate::crate_prelude::*;
use crate::{
    mir::{
        assign::*,
        lower,
        lvalue::{Lvalue, LvalueKind},
        rvalue::{BinaryBitwiseOp, IntBinaryArithOp, Rvalue, ShiftOp},
    },
    ParamEnv,
};

/// Lower a procedural assign statement.
#[moore_derive::query]
pub(crate) fn mir_assignment_of_procedural_stmt<'a>(
    cx: &impl Context<'a>,
    origin: NodeId,
    lhs: NodeId,
    rhs: NodeId,
    env: ParamEnv,
    span: Span,
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
    trace!("Simplifying {:#?} = {:#?}", lhs, rhs);
    match lhs.kind {
        LvalueKind::Concat(ref values) if values.len() == 1 => {
            let mut a = root.clone();
            a.lhs = values[0];
            into.push(cx.arena().alloc_mir_assignment(a));
        }
        LvalueKind::Concat(ref values) => {
            bug_span!(root.span, cx, "assignment to concatenation not implemented");
        }
        _ => {
            into.push(root);
        }
    }
}
