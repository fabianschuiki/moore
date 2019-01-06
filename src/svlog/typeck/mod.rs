// Copyright (c) 2016-2019 Fabian Schuiki

use crate::{crate_prelude::*, hir::HirNode, ty::Type};

pub(crate) fn type_of<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<Type<'gcx>> {
    let hir = cx.hir_of(node_id)?;

    #[allow(unreachable_patterns)]
    match hir {
        HirNode::Port(p) => cx.type_of(p.ty),
        HirNode::Type(hir) => match hir.kind {
            hir::TypeKind::Builtin(hir::BuiltinType::Void) => Ok(cx.mkty_void()),
            hir::TypeKind::Builtin(hir::BuiltinType::Bit) => Ok(cx.mkty_bit()),
            hir::TypeKind::Named(name) => {
                let binding =
                    cx.resolve_upwards_or_error(name, cx.parent_node_id(node_id).unwrap())?;
                Ok(cx.mkty_named(name, binding))
            }
            _ => cx.unimp_msg("type analysis of", hir),
        },
        HirNode::TypeParam(param) => {
            // TODO: check if the parameter has been overridden.
            if let Some(default) = param.default {
                return cx.type_of(default);
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
        _ => cx.unimp_msg("type analysis of", &hir),
    }
}
