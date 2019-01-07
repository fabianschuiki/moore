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
            hir::TypeKind::Named(name) => {
                let binding =
                    cx.resolve_upwards_or_error(name, cx.parent_node_id(node_id).unwrap())?;
                Ok(cx.mkty_named(name, (binding, env)))
            }
            _ => cx.unimp_msg("type analysis of", hir),
        },
        HirNode::TypeParam(param) => {
            // TODO: check if the parameter has been overridden.
            if let Some(default) = param.default {
                return cx.map_to_type(default, env);
            }
            cx.emit(
                DiagBuilder2::error(format!(
                    "`{}` not assigned and has no default",
                    param.name.value
                ))
                .span(param.human_span()),
            );
            Err(())
        }
        _ => cx.unimp_msg("conversion to type of", &hir),
    }
}
