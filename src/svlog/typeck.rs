// Copyright (c) 2016-2019 Fabian Schuiki

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{Type, TypeKind},
    value::ValueKind,
    ParamEnv, ParamEnvBinding,
};
use num::traits::{cast::ToPrimitive, sign::Signed};

/// Determine the type of a node.
pub(crate) fn type_of<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Type<'gcx>> {
    let hir = cx.hir_of(node_id)?;
    #[allow(unreachable_patterns)]
    match hir {
        HirNode::Port(p) => cx.map_to_type(p.ty, env),
        HirNode::Expr(e) => match e.kind {
            hir::ExprKind::IntConst(width, _) => Ok(cx.mkty_int(width)),
            hir::ExprKind::UnsizedConst(_) => Ok(cx.mkty_int(1)),
            hir::ExprKind::TimeConst(_) => Ok(cx.mkty_time()),
            hir::ExprKind::Ident(_) => cx.type_of(cx.resolve_node(node_id, env)?, env),
            hir::ExprKind::Unary(op, arg) => {
                let arg_ty = cx.type_of(arg, env)?;
                Ok(match op {
                    hir::UnaryOp::Neg
                    | hir::UnaryOp::BitNot
                    | hir::UnaryOp::PreInc
                    | hir::UnaryOp::PreDec
                    | hir::UnaryOp::PostInc
                    | hir::UnaryOp::PostDec => arg_ty,
                    hir::UnaryOp::LogicNot => cx.mkty_bit(),
                    _ => return cx.unimp_msg("type analysis of", &hir),
                })
            }
            hir::ExprKind::Binary(op, lhs, rhs) => {
                let lhs_ty = cx.type_of(lhs, env)?;
                let _rhs_ty = cx.type_of(rhs, env)?;
                Ok(match op {
                    hir::BinaryOp::Add
                    | hir::BinaryOp::Sub
                    | hir::BinaryOp::Mul
                    | hir::BinaryOp::Div
                    | hir::BinaryOp::Mod
                    | hir::BinaryOp::Pow
                    | hir::BinaryOp::LogicShL
                    | hir::BinaryOp::LogicShR
                    | hir::BinaryOp::ArithShL
                    | hir::BinaryOp::ArithShR => lhs_ty,
                    hir::BinaryOp::Eq
                    | hir::BinaryOp::Neq
                    | hir::BinaryOp::Lt
                    | hir::BinaryOp::Leq
                    | hir::BinaryOp::Gt
                    | hir::BinaryOp::Geq
                    | hir::BinaryOp::LogicAnd
                    | hir::BinaryOp::LogicOr => cx.mkty_bit(),
                    _ => return cx.unimp_msg("type analysis of", &hir),
                })
            }
            hir::ExprKind::Field(..) => {
                let (_, _, field_id) = cx.resolve_field_access(node_id, env)?;
                cx.type_of(field_id, env)
            }
            hir::ExprKind::Index(target, mode) => {
                let target_ty = cx.type_of(target, env)?;
                match mode {
                    hir::IndexMode::One(..) => match *target_ty {
                        TypeKind::PackedArray(_, ty) => Ok(ty),
                        _ => {
                            let hir = cx.hir_of(target)?;
                            cx.emit(
                                DiagBuilder2::error(format!(
                                    "{} cannot be indexed into",
                                    hir.desc_full()
                                ))
                                .span(hir.human_span()),
                            );
                            Err(())
                        }
                    },
                    hir::IndexMode::Many(..) => Ok(target_ty),
                }
            }
            hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(_))
            | hir::ExprKind::Builtin(hir::BuiltinCall::Bits(_)) => Ok(cx.mkty_int(32)),
            hir::ExprKind::Ternary(_cond, true_expr, _false_expr) => cx.type_of(true_expr, env),
            _ => {
                error!("{:#?}", hir);
                cx.unimp_msg("type analysis of", &hir)
            }
        },
        HirNode::ValueParam(p) => {
            if is_explicit_type(cx, p.ty)? {
                return cx.map_to_type(p.ty, env);
            }
            let env_data = cx.param_env_data(env);
            match env_data.find_value(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.type_of(assigned_id.0, assigned_id.1)
                }
                Some(ParamEnvBinding::Direct(t)) => return Ok(t.ty),
                _ => (),
            }
            if let Some(default) = p.default {
                return cx.type_of(default, env);
            }
            cx.emit(
                DiagBuilder2::error(format!(
                    "{} has implicit type but was not assigned and has no default",
                    p.desc_full()
                ))
                .span(p.human_span())
                .add_note("specify a type for the parameter; or")
                .add_note("add a default value for the parameter; or")
                .add_note("override the parameter from outside"),
            );
            Err(())
        }
        HirNode::VarDecl(d) => {
            if is_explicit_type(cx, d.ty)? {
                cx.map_to_type(d.ty, env)
            } else if let Some(init) = d.init {
                cx.type_of(init, env)
            } else {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "{} has implicit type but is not initialized",
                        d.desc_full()
                    ))
                    .span(d.human_span())
                    .add_note("specify a type for the variable; or")
                    .add_note("add an initial value"),
                );
                Err(())
            }
        }
        HirNode::GenvarDecl(_) => Ok(cx.mkty_int(32)),
        _ => cx.unimp_msg("type analysis of", &hir),
    }
}

/// Convert a node to a type.
pub(crate) fn map_to_type<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Type<'gcx>> {
    let hir = cx.hir_of(node_id)?;
    #[allow(unreachable_patterns)]
    match hir {
        HirNode::Type(hir) => map_type_kind(cx, node_id, env, hir, &hir.kind),
        HirNode::TypeParam(param) => {
            let env_data = cx.param_env_data(env);
            match env_data.find_type(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.map_to_type(assigned_id.0, assigned_id.1)
                }
                Some(ParamEnvBinding::Direct(t)) => return Ok(t),
                _ => (),
            }
            if let Some(default) = param.default {
                return cx.map_to_type(default, env);
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
        HirNode::Typedef(def) => cx.map_to_type(def.ty, env),
        _ => cx.unimp_msg("conversion to type of", &hir),
    }
}

/// Check if a type (given by its node id) is explicit.
fn is_explicit_type<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<bool> {
    Ok(match cx.hir_of(node_id)? {
        HirNode::Type(x) => x.is_explicit(),
        _ => false,
    })
}

/// Map an HIR type into the type system.
///
/// This essentially converts `hir::TypeKind` to `Type`.
fn map_type_kind<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
    root: &hir::Type,
    kind: &hir::TypeKind,
) -> Result<Type<'gcx>> {
    #[allow(unreachable_patterns)]
    match *kind {
        hir::TypeKind::Builtin(hir::BuiltinType::Void) => Ok(cx.mkty_void()),
        hir::TypeKind::Builtin(hir::BuiltinType::Bit) => Ok(cx.mkty_bit()),
        hir::TypeKind::Builtin(hir::BuiltinType::Logic) => Ok(cx.mkty_logic()),
        hir::TypeKind::Builtin(hir::BuiltinType::Byte) => Ok(cx.mkty_int(8)),
        hir::TypeKind::Builtin(hir::BuiltinType::ShortInt) => Ok(cx.mkty_int(16)),
        hir::TypeKind::Builtin(hir::BuiltinType::Int) => Ok(cx.mkty_int(32)),
        hir::TypeKind::Builtin(hir::BuiltinType::LongInt) => Ok(cx.mkty_int(64)),
        hir::TypeKind::Named(name) => {
            let binding = cx.resolve_upwards_or_error(name, cx.parent_node_id(node_id).unwrap())?;
            Ok(cx.mkty_named(name, (binding, env)))
        }
        hir::TypeKind::Struct(..) => Ok(cx.mkty_struct(node_id)),
        hir::TypeKind::PackedArray(ref inner, lhs, rhs) => {
            let map_bound = |bound: NodeId| -> Result<&num::BigInt> {
                match cx.constant_value_of(bound, env)?.kind {
                    ValueKind::Int(ref int) => Ok(int),
                    _ => {
                        let span = cx.span(bound);
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "array bound `{}` is not an integer",
                                span.extract()
                            ))
                            .span(span),
                        );
                        return Err(());
                    }
                }
            };
            let size: num::BigInt = (map_bound(lhs)? - map_bound(rhs)?).abs();
            let size = match size.to_usize() {
                Some(i) => i + 1,
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!("{} is too large", kind.desc_full()))
                            .span(root.human_span())
                            .add_note(format!("array would contain {} elements", size)),
                    );
                    return Err(());
                }
            };
            match **inner {
                hir::TypeKind::Builtin(hir::BuiltinType::Bit) => Ok(cx.mkty_int(size)),
                hir::TypeKind::Builtin(hir::BuiltinType::Logic) => Ok(cx.mkty_integer(size)),
                _ => {
                    let inner_ty = map_type_kind(cx, node_id, env, root, inner)?;
                    Ok(cx.mkty_packed_array(size, inner_ty))
                }
            }
        }
        // We should never request mapping of an implicit type. Rather, the
        // actual type should be mapped. Arriving here is a bug in the
        // calling function.
        hir::TypeKind::Implicit => unreachable!("implicit type not resolved"),
        _ => cx.unimp_msg("type analysis of", root),
    }
}
