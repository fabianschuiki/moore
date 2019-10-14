// Copyright (c) 2016-2019 Fabian Schuiki

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
use num::{BigInt, BigRational, One, ToPrimitive, Zero};

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

/// The different forms a value can assume.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueKind<'t> {
    /// The `void` value.
    Void,
    /// An arbitrary precision integer.
    Int(BigInt),
    /// An arbitrary precision time interval.
    Time(BigRational),
    /// A struct.
    StructOrArray(Vec<Value<'t>>),
}

impl<'t> ValueData<'t> {
    /// Check if this value evaluates to true.
    pub fn is_true(&self) -> bool {
        !self.is_false()
    }

    /// Check if this value evaluates to false.
    pub fn is_false(&self) -> bool {
        match self.kind {
            ValueKind::Void => true,
            ValueKind::Int(ref v) => v.is_zero(),
            ValueKind::Time(ref v) => v.is_zero(),
            ValueKind::StructOrArray(_) => false,
        }
    }
}

/// Create a new integer value.
///
/// Panics if `ty` is not an integer type. Truncates the value to `ty`.
pub fn make_int(ty: Type, mut value: BigInt) -> ValueData {
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
        kind: ValueKind::Int(value),
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
        hir::ExprKind::IntConst(_, ref k) => Ok(cx.intern_value(make_int(ty, k.clone()))),
        hir::ExprKind::UnsizedConst('0') => Ok(cx.intern_value(make_int(ty, num::zero()))),
        hir::ExprKind::UnsizedConst('1') => Ok(cx.intern_value(make_int(ty, num::one()))),
        hir::ExprKind::TimeConst(ref k) => Ok(cx.intern_value(make_time(k.clone()))),
        hir::ExprKind::Ident(_) | hir::ExprKind::Scope(..) => {
            let binding = cx.resolve_node(expr.id, env)?;
            match cx.constant_value_of(binding, env) {
                Ok(k) => Ok(k),
                Err(_) => {
                    let hir = cx.hir_of(binding)?;
                    cx.emit(
                        DiagBuilder2::note(format!(
                            "constant value of {} needed here",
                            hir.desc_full()
                        ))
                        .span(cx.span(expr.id)),
                    );
                    Err(())
                }
            }
        }
        hir::ExprKind::Unary(op, arg) => {
            let arg_val = cx.constant_value_of(arg, env)?;
            debug!("exec {:?}({:?})", op, arg_val);
            match arg_val.kind {
                ValueKind::Int(ref arg) => Ok(cx.intern_value(make_int(
                    ty,
                    const_unary_op_on_int(cx, expr.span, ty, op, arg)?,
                ))),
                _ => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "{} cannot be applied to the given arguments",
                            op.desc_full(),
                        ))
                        .span(expr.span()),
                    );
                    Err(())
                }
            }
        }
        hir::ExprKind::Binary(op, lhs, rhs) => {
            let lhs_val = cx.constant_value_of(lhs, env)?;
            let rhs_val = cx.constant_value_of(rhs, env)?;
            debug!("exec {:?}({:?}, {:?})", op, lhs_val, rhs_val);
            match (&lhs_val.kind, &rhs_val.kind) {
                (&ValueKind::Int(ref lhs), &ValueKind::Int(ref rhs)) => Ok(cx.intern_value(
                    make_int(ty, const_binary_op_on_int(cx, expr.span, ty, op, lhs, rhs)?),
                )),
                _ => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "{} cannot be applied to the given arguments",
                            op.desc_full(),
                        ))
                        .span(expr.span()),
                    );
                    Err(())
                }
            }
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(arg)) => {
            let arg_val = cx.constant_value_of(arg, env)?;
            let arg_int = match arg_val.kind {
                ValueKind::Int(ref arg) => arg,
                _ => unreachable!(),
            };
            let value: BigInt = if arg_int <= &num::zero() {
                num::zero()
            } else {
                arg_int.bits().into()
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
        hir::ExprKind::Ternary(cond, true_expr, false_expr) => {
            let cond_val = cx.constant_value_of(cond, env)?;
            match cond_val.is_true() {
                true => cx.constant_value_of(true_expr, env),
                false => cx.constant_value_of(false_expr, env),
            }
        }
        hir::ExprKind::Field(target, _field_name) => {
            let (_, field_index, _) = cx.resolve_field_access(expr.id, env)?;
            let target_value = cx.constant_value_of(target, env)?;
            match target_value.kind {
                ValueKind::StructOrArray(ref fields) => Ok(fields[field_index]),
                _ => Err(()),
            }
        }
        hir::ExprKind::PositionalPattern(..)
        | hir::ExprKind::NamedPattern(..)
        | hir::ExprKind::RepeatPattern(..) => {
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
        _ => cx.unimp_msg("constant value computation of", expr),
    }
}

fn const_unary_op_on_int<'gcx>(
    cx: &impl Context<'gcx>,
    span: Span,
    ty: Type<'gcx>,
    op: hir::UnaryOp,
    arg: &BigInt,
) -> Result<BigInt> {
    Ok(match op {
        hir::UnaryOp::Pos => arg.clone(),
        hir::UnaryOp::Neg => -arg,
        hir::UnaryOp::BitNot => (BigInt::one() << ty.width()) - 1 - arg,
        hir::UnaryOp::LogicNot => (arg.is_zero() as usize).into(),
        _ => {
            cx.emit(
                DiagBuilder2::error(format!(
                    "{} cannot be applied to integer `{}`",
                    op.desc_full(),
                    arg,
                ))
                .span(span),
            );
            return Err(());
        }
    })
}

fn const_binary_op_on_int<'gcx>(
    cx: &impl Context<'gcx>,
    span: Span,
    _ty: Type<'gcx>,
    op: hir::BinaryOp,
    lhs: &BigInt,
    rhs: &BigInt,
) -> Result<BigInt> {
    Ok(match op {
        hir::BinaryOp::Add => lhs + rhs,
        hir::BinaryOp::Sub => lhs - rhs,
        hir::BinaryOp::Mul => lhs * rhs,
        hir::BinaryOp::Div => lhs / rhs,
        hir::BinaryOp::Mod => lhs % rhs,
        hir::BinaryOp::Pow => {
            let mut result = num::one();
            let mut cnt = rhs.clone();
            while !cnt.is_zero() {
                result = result * lhs;
                cnt = cnt - 1;
            }
            result
        }
        hir::BinaryOp::Eq => ((lhs == rhs) as usize).into(),
        hir::BinaryOp::Neq => ((lhs != rhs) as usize).into(),
        hir::BinaryOp::Lt => ((lhs < rhs) as usize).into(),
        hir::BinaryOp::Leq => ((lhs <= rhs) as usize).into(),
        hir::BinaryOp::Gt => ((lhs > rhs) as usize).into(),
        hir::BinaryOp::Geq => ((lhs >= rhs) as usize).into(),
        hir::BinaryOp::LogicShL | hir::BinaryOp::ArithShL => match rhs.to_isize() {
            Some(sh) if sh < 0 => lhs >> -sh as usize,
            Some(sh) => lhs << sh as usize,
            None => num::zero(),
        },
        hir::BinaryOp::LogicShR | hir::BinaryOp::ArithShR => match rhs.to_isize() {
            Some(sh) if sh < 0 => lhs << -sh as usize,
            Some(sh) => lhs >> sh as usize,
            None => num::zero(),
        },
        _ => {
            cx.emit(
                DiagBuilder2::error(format!(
                    "{} cannot be applied to integers `{}` and `{}`",
                    op.desc_full(),
                    lhs,
                    rhs
                ))
                .span(span),
            );
            return Err(());
        }
    })
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
