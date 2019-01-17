// Copyright (c) 2016-2019 Fabian Schuiki

use crate::{crate_prelude::*, hir::HirNode, ty::Type, ParamEnv};

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
            hir::ExprKind::IntConst(_) => Ok(cx.mkty_int(32)),
            hir::ExprKind::TimeConst(_) => Ok(cx.mkty_time()),
            hir::ExprKind::Ident(_) => cx.type_of(cx.resolve_node(node_id, env)?, env),
            hir::ExprKind::Unary(op, arg) => {
                let arg_ty = cx.type_of(arg, env)?;
                Ok(match op {
                    hir::UnaryOp::BitNot
                    | hir::UnaryOp::PreInc
                    | hir::UnaryOp::PreDec
                    | hir::UnaryOp::PostInc
                    | hir::UnaryOp::PostDec => arg_ty,
                    _ => return cx.unimp_msg("type analysis of", &hir),
                })
            }
            hir::ExprKind::Binary(op, lhs, rhs) => {
                let lhs_ty = cx.type_of(lhs, env)?;
                let _rhs_ty = cx.type_of(rhs, env)?;
                Ok(match op {
                    hir::BinaryOp::Add | hir::BinaryOp::Sub => lhs_ty,
                    _ => return cx.unimp_msg("type analysis of", &hir),
                })
            }
            _ => cx.unimp_msg("type analysis of", &hir),
        },
        HirNode::ValueParam(p) => cx.map_to_type(p.ty, env),
        HirNode::VarDecl(d) => cx.map_to_type(d.ty, env),
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
        HirNode::Type(hir) => match hir.kind {
            hir::TypeKind::Builtin(hir::BuiltinType::Void) => Ok(cx.mkty_void()),
            hir::TypeKind::Builtin(hir::BuiltinType::Bit) => Ok(cx.mkty_bit()),
            hir::TypeKind::Builtin(hir::BuiltinType::Logic) => Ok(cx.mkty_logic()),
            hir::TypeKind::Builtin(hir::BuiltinType::Byte) => Ok(cx.mkty_int(8)),
            hir::TypeKind::Builtin(hir::BuiltinType::ShortInt) => Ok(cx.mkty_int(16)),
            hir::TypeKind::Builtin(hir::BuiltinType::Int) => Ok(cx.mkty_int(32)),
            hir::TypeKind::Builtin(hir::BuiltinType::LongInt) => Ok(cx.mkty_int(64)),
            hir::TypeKind::Named(name) => {
                let binding =
                    cx.resolve_upwards_or_error(name, cx.parent_node_id(node_id).unwrap())?;
                Ok(cx.mkty_named(name, (binding, env)))
            }
            _ => cx.unimp_msg("type analysis of", hir),
        },
        HirNode::TypeParam(param) => {
            let env_data = cx.param_env_data(env);
            if let Some(assigned_id) = env_data.find_type(node_id) {
                return cx.map_to_type(assigned_id.0, assigned_id.1);
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
        _ => cx.unimp_msg("conversion to type of", &hir),
    }
}
