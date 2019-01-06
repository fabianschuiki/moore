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
        _ => cx.unimp_msg("type analysis of", &hir),
    }
}
