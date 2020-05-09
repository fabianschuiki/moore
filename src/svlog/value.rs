// Copyright (c) 2016-2020 Fabian Schuiki

//! Representation of constant values and their operations
//!
//! This module implements a representation for values that may arise within a
//! SystemVerilog source text and provides ways of executing common operations
//! such as addition and multiplication. It also provides the ability to
//! evaluate the constant value of nodes in a context.
//!
//! The operations in this module are intended to panic if invalid combinations
//! of values are used. The compiler's type system should catch and prevent such
//! uses.

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{bit_size_of_type, Type, TypeKind},
    ParamEnv, ParamEnvBinding,
};
use bit_vec::BitVec;
use num::{BigInt, BigRational, Integer, One, ToPrimitive, Zero};

/// A verilog value.
pub type Value<'t> = &'t ValueData<'t>;

/// The data associated with a value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValueData<'t> {
    /// The type of the value.
    pub ty: Type<'t>,
    /// The actual value.
    pub kind: ValueKind<'t>,
}

impl<'t> ValueData<'t> {
    /// Check if the value represents a computation error tombstone.
    pub fn is_error(&self) -> bool {
        self.ty.is_error() || self.kind.is_error()
    }

    /// Check if this value evaluates to true.
    pub fn is_true(&self) -> bool {
        !self.is_false()
    }

    /// Check if this value evaluates to false.
    pub fn is_false(&self) -> bool {
        match self.kind {
            ValueKind::Void => true,
            ValueKind::Int(ref v, ..) => v.is_zero(),
            ValueKind::Time(ref v) => v.is_zero(),
            ValueKind::StructOrArray(_) => false,
            ValueKind::Error => true,
        }
    }

    /// Convert the value to an integer.
    pub fn get_int(&self) -> Option<&BigInt> {
        match self.kind {
            ValueKind::Int(ref v, ..) => Some(v),
            _ => None,
        }
    }
}

/// The different forms a value can assume.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueKind<'t> {
    /// The `void` value.
    Void,
    /// An arbitrary precision integer.
    ///
    /// The first field contains the value. The second field indicates the
    /// special bits (x or z), and the third indicates the x bits.
    Int(BigInt, BitVec, BitVec),
    /// An arbitrary precision time interval.
    Time(BigRational),
    /// A struct.
    StructOrArray(Vec<Value<'t>>),
    /// An error occurred during value computation.
    Error,
}

impl<'t> ValueKind<'t> {
    /// Check if the value represents a computation error tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            ValueKind::Error => true,
            _ => false,
        }
    }
}

/// Create a new tombstone value.
pub fn make_error(ty: Type) -> ValueData {
    ValueData {
        ty,
        kind: ValueKind::Error,
    }
}

/// Create a new integer value.
///
/// Panics if `ty` is not an integer type. Truncates the value to `ty`.
pub fn make_int(ty: Type, value: BigInt) -> ValueData {
    let w = ty.width();
    make_int_special(
        ty,
        value,
        BitVec::from_elem(w, false),
        BitVec::from_elem(w, false),
    )
}

/// Create a new integer value with special bits.
///
/// Panics if `ty` is not an integer type. Truncates the value to `ty`.
pub fn make_int_special(
    ty: Type,
    mut value: BigInt,
    special_bits: BitVec,
    x_bits: BitVec,
) -> ValueData {
    match *ty {
        TypeKind::Int(width, _)
        | TypeKind::BitVector {
            range: ty::Range { size: width, .. },
            ..
        } => {
            value = value % (BigInt::from(1) << width);
        }
        TypeKind::Bit(_) | TypeKind::BitScalar { .. } => {
            value = value % 2;
        }
        _ => panic!("create int value `{}` with non-int type {:?}", value, ty),
    }
    ValueData {
        ty: ty,
        kind: ValueKind::Int(value, special_bits, x_bits),
    }
}

/// Create a new time value.
pub fn make_time(value: BigRational) -> ValueData<'static> {
    ValueData {
        ty: &ty::TIME_TYPE,
        kind: ValueKind::Time(value),
    }
}

/// Create a new struct value.
pub fn make_struct<'t>(ty: Type<'t>, fields: Vec<Value<'t>>) -> ValueData<'t> {
    assert!(ty.is_struct());
    ValueData {
        ty: ty,
        kind: ValueKind::StructOrArray(fields),
    }
}

/// Create a new array value.
pub fn make_array<'t>(ty: Type<'t>, elements: Vec<Value<'t>>) -> ValueData<'t> {
    assert!(ty.is_array());
    ValueData {
        ty: ty,
        kind: ValueKind::StructOrArray(elements),
    }
}

/// Determine the constant value of a node.
pub(crate) fn constant_value_of<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Value<'gcx>> {
    let hir = cx.hir_of(node_id)?;
    match hir {
        HirNode::Expr(expr) => const_expr(cx, expr, env),
        HirNode::ValueParam(param) => {
            let env_data = cx.param_env_data(env);
            match env_data.find_value(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.constant_value_of(assigned_id.0, assigned_id.1)
                }
                Some(ParamEnvBinding::Direct(v)) => return Ok(v),
                _ => (),
            }
            if let Some(default) = param.default {
                return cx.constant_value_of(default, env);
            }
            let mut d = DiagBuilder2::error(format!(
                "{} not assigned and has no default",
                param.desc_full(),
            ));
            let contexts = cx.param_env_contexts(env);
            for &context in &contexts {
                d = d.span(cx.span(context));
            }
            if contexts.is_empty() {
                d = d.span(param.human_span());
            }
            cx.emit(d);
            Err(())
        }
        HirNode::GenvarDecl(decl) => {
            let env_data = cx.param_env_data(env);
            match env_data.find_value(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.constant_value_of(assigned_id.0, assigned_id.1)
                }
                Some(ParamEnvBinding::Direct(v)) => return Ok(v),
                _ => (),
            }
            if let Some(init) = decl.init {
                return cx.constant_value_of(init, env);
            }
            cx.emit(
                DiagBuilder2::error(format!("{} not initialized", decl.desc_full()))
                    .span(decl.human_span()),
            );
            Err(())
        }
        HirNode::VarDecl(_) => {
            cx.emit(
                DiagBuilder2::error(format!("{} has no constant value", hir.desc_full()))
                    .span(hir.human_span()),
            );
            Err(())
        }
        HirNode::EnumVariant(var) => match var.value {
            Some(v) => cx.constant_value_of(v, env),
            None => Ok(cx.intern_value(make_int(cx.type_of(node_id, env)?, var.index.into()))),
        },
        _ => cx.unimp_msg("constant value computation of", &hir),
    }
}

/// Determine the constant value of an expression.
fn const_expr<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &hir::Expr,
    env: ParamEnv,
) -> Result<Value<'gcx>> {
    let ty = cx.type_of(expr.id, env)?;
    #[allow(unreachable_patterns)]
    match expr.kind {
        hir::ExprKind::IntConst {
            value: ref k,
            ref special_bits,
            ref x_bits,
            ..
        } => Ok(cx.intern_value(make_int_special(
            ty,
            k.clone(),
            special_bits.clone(),
            x_bits.clone(),
        ))),
        hir::ExprKind::UnsizedConst('0') => Ok(cx.intern_value(make_int(ty, num::zero()))),
        hir::ExprKind::UnsizedConst('1') => Ok(cx.intern_value(make_int(ty, num::one()))),
        hir::ExprKind::TimeConst(ref k) => Ok(cx.intern_value(make_time(k.clone()))),
        hir::ExprKind::StringConst(_) => Ok(cx.intern_value(make_array(
            // TODO(fschuiki): Actually assemble a real string here!
            cx.mkty_packed_array(1, &ty::BYTE_TYPE),
            vec![cx.intern_value(make_int(&ty::BYTE_TYPE, num::zero()))],
        ))),
        hir::ExprKind::Builtin(hir::BuiltinCall::Unsupported) => {
            Ok(cx.intern_value(make_int(ty, num::zero())))
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(arg)) => {
            let arg_val = cx.constant_value_of(arg, env)?;
            let arg_int = match arg_val.kind {
                ValueKind::Int(ref arg, ..) => arg,
                _ => unreachable!(),
            };
            let value = if arg_int <= &BigInt::one() {
                BigInt::zero()
            } else {
                BigInt::from((arg_int - BigInt::one()).bits())
            };
            Ok(cx.intern_value(make_int(arg_val.ty, value)))
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::Bits(arg)) => {
            let ty = cx.type_of(arg, env)?;
            Ok(cx.intern_value(make_int(
                cx.mkty_int(32),
                bit_size_of_type(cx, ty, env)?.into(),
            )))
        }
        hir::ExprKind::Field(target, _field_name) => {
            let (_, field_index, _) = cx.resolve_field_access(expr.id, env)?;
            let target_value = cx.constant_value_of(target, env)?;
            match target_value.kind {
                ValueKind::StructOrArray(ref fields) => Ok(fields[field_index]),
                _ => Err(()),
            }
        }
        hir::ExprKind::PositionalPattern(..) | hir::ExprKind::RepeatPattern(..) => {
            let mut resolved = resolver::resolve_pattern(cx, expr.id, env)?;
            resolved.sort_by(|(a, _), (b, _)| a.cmp(b));
            trace!("resolved {:?} to {:#?}", expr.kind, resolved);
            let fields = resolved
                .into_iter()
                .map(|(_, v)| cx.constant_value_of(v, env))
                .collect::<Result<Vec<_>>>()?;
            let ty = cx.type_of(expr.id, env)?;
            let v = cx.intern_value(match *ty {
                TypeKind::Named(_, _, TypeKind::Struct(..)) | TypeKind::Struct(..) => {
                    make_struct(ty, fields)
                }
                TypeKind::Named(_, _, TypeKind::PackedArray(..)) | TypeKind::PackedArray(..) => {
                    make_array(ty, fields)
                }
                _ => unreachable!(),
            });
            trace!("pattern yielded {:#?}", v);
            Ok(v)
        }
        hir::ExprKind::EmptyPattern => {
            cx.emit(
                DiagBuilder2::error(format!("{} has no constant value", expr.desc_full()))
                    .span(expr.span()),
            );
            Err(())
        }
        _ => {
            let mir = cx.mir_rvalue(expr.id, env);
            Ok(const_mir(cx, mir))
            // error!("{:?}", expr);
            // cx.unimp_msg("constant value computation of", expr)
        }
    }
}

fn const_mir<'gcx>(cx: &impl Context<'gcx>, mir: &'gcx mir::Rvalue<'gcx>) -> Value<'gcx> {
    match mir.kind {
        // TODO: Casts are just transparent at the moment. That's pretty bad.
        mir::RvalueKind::CastValueDomain { value, .. }
        | mir::RvalueKind::CastVectorToAtom { value, .. }
        | mir::RvalueKind::CastAtomToVector { value, .. }
        | mir::RvalueKind::CastSign(_, value)
        | mir::RvalueKind::Truncate(_, value)
        | mir::RvalueKind::ZeroExtend(_, value)
        | mir::RvalueKind::SignExtend(_, value) => {
            cx.emit(
                DiagBuilder2::warning("cast ignored during constant evaluation")
                    .span(mir.span)
                    .add_note(format!(
                        "Casts `{}` from `{}` to `{}`",
                        value.span.extract(),
                        value.ty,
                        mir.ty
                    ))
                    .span(value.span),
            );
            const_mir(cx, value)
        }

        mir::RvalueKind::CastToBool(value) => {
            let value = const_mir(cx, value);
            if value.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            cx.intern_value(make_int(mir.ty, (value.is_true() as usize).into()))
        }

        mir::RvalueKind::ConstructArray(ref values) => cx.intern_value(make_array(
            mir.ty,
            (0..values.len())
                .map(|index| const_mir(cx, values[&index]))
                .collect(),
        )),

        mir::RvalueKind::ConstructStruct(ref values) => cx.intern_value(make_struct(
            mir.ty,
            values.iter().map(|value| const_mir(cx, value)).collect(),
        )),

        mir::RvalueKind::Const(value) => value,

        mir::RvalueKind::UnaryBitwise { op, arg } => {
            let arg_val = const_mir(cx, arg);
            if arg_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match arg_val.kind {
                ValueKind::Int(ref arg_int, ..) => cx.intern_value(make_int(
                    mir.ty,
                    const_unary_bitwise_int(cx, arg.ty, op, arg_int),
                )),
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::BinaryBitwise { op, lhs, rhs } => {
            let lhs_val = const_mir(cx, lhs);
            let rhs_val = const_mir(cx, rhs);
            if lhs_val.is_error() || rhs_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match (&lhs_val.kind, &rhs_val.kind) {
                (ValueKind::Int(lhs_int, ..), ValueKind::Int(rhs_int, ..)) => {
                    cx.intern_value(make_int(
                        mir.ty,
                        const_binary_bitwise_int(cx, lhs.ty, op, lhs_int, rhs_int),
                    ))
                }
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::IntUnaryArith { op, arg, .. } => {
            let arg_val = const_mir(cx, arg);
            if arg_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match arg_val.kind {
                ValueKind::Int(ref arg_int, ..) => cx.intern_value(make_int(
                    mir.ty,
                    const_unary_arith_int(cx, arg.ty, op, arg_int),
                )),
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::IntBinaryArith { op, lhs, rhs, .. } => {
            let lhs_val = const_mir(cx, lhs);
            let rhs_val = const_mir(cx, rhs);
            if lhs_val.is_error() || rhs_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match (&lhs_val.kind, &rhs_val.kind) {
                (ValueKind::Int(lhs_int, ..), ValueKind::Int(rhs_int, ..)) => {
                    cx.intern_value(make_int(
                        mir.ty,
                        const_binary_arith_int(cx, lhs.ty, op, lhs_int, rhs_int),
                    ))
                }
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::IntComp { op, lhs, rhs, .. } => {
            let lhs_val = const_mir(cx, lhs);
            let rhs_val = const_mir(cx, rhs);
            if lhs_val.is_error() || rhs_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match (&lhs_val.kind, &rhs_val.kind) {
                (ValueKind::Int(lhs_int, ..), ValueKind::Int(rhs_int, ..)) => cx.intern_value(
                    make_int(mir.ty, const_comp_int(cx, lhs.ty, op, lhs_int, rhs_int)),
                ),
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::Concat(ref values) => {
            let mut result = BigInt::zero();
            for value in values {
                result <<= value.ty.width();
                result |= const_mir(cx, value).get_int().expect("concat non-integer");
            }
            cx.intern_value(make_int(mir.ty, result))
        }

        mir::RvalueKind::Var(id) | mir::RvalueKind::Port(id) => {
            match cx.constant_value_of(id, mir.env) {
                Ok(k) => k,
                Err(_) => {
                    cx.emit(DiagBuilder2::note("constant value needed here").span(mir.span));
                    cx.intern_value(make_error(mir.ty))
                }
            }
        }

        mir::RvalueKind::Ternary {
            cond,
            true_value,
            false_value,
        } => {
            let cond_val = const_mir(cx, cond);
            let true_val = const_mir(cx, true_value);
            let false_val = const_mir(cx, false_value);
            match cond_val.is_true() {
                true => true_val,
                false => false_val,
            }
        }

        mir::RvalueKind::Shift {
            op,
            arith,
            value,
            amount,
            ..
        } => {
            let value_val = const_mir(cx, value);
            let amount_val = const_mir(cx, amount);
            if value_val.is_error() || amount_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match (&value_val.kind, &amount_val.kind) {
                (ValueKind::Int(value_int, ..), ValueKind::Int(amount_int, ..)) => {
                    cx.intern_value(make_int(
                        mir.ty,
                        const_shift_int(cx, value.ty, op, arith, value_int, amount_int),
                    ))
                }
                _ => unreachable!(),
            }
        }

        mir::RvalueKind::Reduction { op, arg } => {
            let arg_val = const_mir(cx, arg);
            if arg_val.is_error() {
                return cx.intern_value(make_error(mir.ty));
            }
            match arg_val.kind {
                ValueKind::Int(ref arg_int, ..) => cx.intern_value(make_int(
                    mir.ty,
                    const_reduction_int(cx, arg.ty, op, arg_int),
                )),
                _ => unreachable!(),
            }
        }

        // Propagate tombstones.
        mir::RvalueKind::Error => cx.intern_value(make_error(mir.ty)),

        // TODO: This should eventually not be necessary, because each MIR is
        // either handled or throws an error.
        _ => {
            cx.emit(DiagBuilder2::bug("constant value of rvalue not implemented").span(mir.span));
            error!("Offending MIR is: {:#?}", mir);
            cx.intern_value(make_error(mir.ty))
        }
    }
}

fn const_unary_bitwise_int<'gcx>(
    _cx: &impl Context<'gcx>,
    ty: Type,
    op: mir::UnaryBitwiseOp,
    arg: &BigInt,
) -> BigInt {
    match op {
        mir::UnaryBitwiseOp::Not => (BigInt::one() << ty.width()) - 1 - arg,
    }
}

fn const_binary_bitwise_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: Type,
    op: mir::BinaryBitwiseOp,
    lhs: &BigInt,
    rhs: &BigInt,
) -> BigInt {
    match op {
        mir::BinaryBitwiseOp::And => lhs & rhs,
        mir::BinaryBitwiseOp::Or => lhs | rhs,
        mir::BinaryBitwiseOp::Xor => lhs ^ rhs,
    }
}

fn const_unary_arith_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: Type,
    op: mir::IntUnaryArithOp,
    arg: &BigInt,
) -> BigInt {
    match op {
        mir::IntUnaryArithOp::Neg => -arg,
    }
}

fn const_binary_arith_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: Type,
    op: mir::IntBinaryArithOp,
    lhs: &BigInt,
    rhs: &BigInt,
) -> BigInt {
    match op {
        mir::IntBinaryArithOp::Add => lhs + rhs,
        mir::IntBinaryArithOp::Sub => lhs - rhs,
        mir::IntBinaryArithOp::Mul => lhs * rhs,
        mir::IntBinaryArithOp::Div => lhs / rhs,
        mir::IntBinaryArithOp::Mod => lhs % rhs,
        mir::IntBinaryArithOp::Pow => {
            let mut result = num::one();
            let mut cnt = rhs.clone();
            while !cnt.is_zero() {
                result = result * lhs;
                cnt = cnt - 1;
            }
            result
        }
    }
}

fn const_comp_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: Type,
    op: mir::IntCompOp,
    lhs: &BigInt,
    rhs: &BigInt,
) -> BigInt {
    match op {
        mir::IntCompOp::Eq => ((lhs == rhs) as usize).into(),
        mir::IntCompOp::Neq => ((lhs != rhs) as usize).into(),
        mir::IntCompOp::Lt => ((lhs < rhs) as usize).into(),
        mir::IntCompOp::Leq => ((lhs <= rhs) as usize).into(),
        mir::IntCompOp::Gt => ((lhs > rhs) as usize).into(),
        mir::IntCompOp::Geq => ((lhs >= rhs) as usize).into(),
    }
}

fn const_shift_int<'gcx>(
    _cx: &impl Context<'gcx>,
    _ty: Type,
    op: mir::ShiftOp,
    _arith: bool,
    value: &BigInt,
    amount: &BigInt,
) -> BigInt {
    match op {
        mir::ShiftOp::Left => match amount.to_isize() {
            Some(sh) if sh < 0 => value >> -sh as usize,
            Some(sh) => value << sh as usize,
            None => num::zero(),
        },
        mir::ShiftOp::Right => match amount.to_isize() {
            Some(sh) if sh < 0 => value << -sh as usize,
            Some(sh) => value >> sh as usize,
            None => num::zero(),
        },
    }
}

fn const_reduction_int<'gcx>(
    _cx: &impl Context<'gcx>,
    ty: Type,
    op: mir::BinaryBitwiseOp,
    arg: &BigInt,
) -> BigInt {
    match op {
        mir::BinaryBitwiseOp::And => {
            ((arg == &((BigInt::one() << ty.width()) - 1)) as usize).into()
        }
        mir::BinaryBitwiseOp::Or => ((!arg.is_zero()) as usize).into(),
        mir::BinaryBitwiseOp::Xor => (arg
            .to_bytes_le()
            .1
            .into_iter()
            .map(|v| v.count_ones())
            .sum::<u32>()
            .is_odd() as usize)
            .into(),
    }
}

/// Check if a node has a constant value.
pub(crate) fn is_constant<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<bool> {
    let hir = cx.hir_of(node_id)?;
    Ok(match hir {
        HirNode::ValueParam(_) => true,
        HirNode::GenvarDecl(_) => true,
        HirNode::EnumVariant(_) => true,
        _ => false,
    })
}

/// Determine the default value of a type.
pub(crate) fn type_default_value<'gcx>(cx: &impl Context<'gcx>, ty: Type<'gcx>) -> Value<'gcx> {
    // TODO(fschuiki): Make this function return `Result<Value<_>>`.
    match *ty {
        TypeKind::Error => cx.intern_value(ValueData {
            ty: &ty::ERROR_TYPE,
            kind: ValueKind::Void,
        }),
        TypeKind::Void => cx.intern_value(ValueData {
            ty: &ty::VOID_TYPE,
            kind: ValueKind::Void,
        }),
        TypeKind::Time => cx.intern_value(make_time(Zero::zero())),
        TypeKind::Bit(..)
        | TypeKind::Int(..)
        | TypeKind::BitVector { .. }
        | TypeKind::BitScalar { .. } => cx.intern_value(make_int(ty, Zero::zero())),
        TypeKind::Named(_, _, ty) => type_default_value(cx, ty),
        TypeKind::Struct(id) => {
            let def = cx.struct_def(id).unwrap();
            let fields = def
                .fields
                .iter()
                .map(|field| {
                    type_default_value(
                        cx,
                        cx.map_to_type(field.ty, cx.default_param_env()).unwrap(),
                    )
                })
                .collect();
            cx.intern_value(make_struct(ty, fields))
        }
        TypeKind::PackedArray(length, elem_ty) => cx.intern_value(make_array(
            ty.clone(),
            std::iter::repeat(cx.type_default_value(elem_ty.clone()))
                .take(length)
                .collect(),
        )),
    }
}
