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
    ty::{Type, TypeKind},
    ParamEnv,
};
use num::{BigInt, Zero};

/// A verilog value.
pub type Value<'t> = &'t ValueData<'t>;

/// The data associated with a value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValueData<'t> {
    /// The type of the value.
    pub ty: Type<'t>,
    /// The actual value.
    pub kind: ValueKind,
}

/// The different forms a value can assume.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueKind {
    /// The `void` value.
    Void,
    /// An arbitrary precision integer.
    Int(BigInt),
}

/// Create a new integer value.
///
/// Panics if `ty` is not an integer type. Truncates the value to `ty`.
pub fn make_int(ty: Type, mut value: BigInt) -> ValueData {
    match *ty {
        TypeKind::Int(width, _) => {
            value = value % (BigInt::from(1) << width);
        }
        TypeKind::Bit(_) => {
            value = value % 2;
        }
        _ => panic!("create int value `{}` with non-int type {:?}", value, ty),
    }
    ValueData {
        ty: ty,
        kind: ValueKind::Int(value),
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
            if let Some(assigned_id) = env_data.find_value(node_id) {
                return cx.constant_value_of(assigned_id.0, assigned_id.1);
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
        hir::ExprKind::IntConst(ref k) => Ok(cx.intern_value(make_int(ty, k.clone()))),
        hir::ExprKind::Ident(_) => cx.constant_value_of(cx.resolve_node(expr.id, env)?, env),
        _ => cx.unimp_msg("constant value computation of", expr),
    }
}

/// Determine the default value of a type.
pub(crate) fn type_default_value<'gcx>(cx: &impl Context<'gcx>, ty: Type<'gcx>) -> Value<'gcx> {
    match *ty {
        TypeKind::Void => cx.intern_value(ValueData {
            ty,
            kind: ValueKind::Void,
        }),
        TypeKind::Bit(..) | TypeKind::Int(..) => cx.intern_value(make_int(ty, Zero::zero())),
        TypeKind::Named(_, _, ty) => type_default_value(cx, ty),
    }
}
