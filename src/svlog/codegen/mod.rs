// Copyright (c) 2016-2019 Fabian Schuiki

//! This module implements LLHD code generation.

use crate::crate_prelude::*;
use crate::hir::HirNode;

pub(crate) fn generate_code<'gcx>(cx: Context<'gcx>, node_id: NodeId) -> Result<llhd::Module> {
    debug!("generate_code({})", node_id);

    let hir = cx.hir_of(node_id)?;

    let mut module = llhd::Module::new();
    #[allow(unreachable_patterns)]
    match hir {
        HirNode::Module(m) => {
            codegen_module(cx, m, &mut module)?;
        }
        _ => {
            cx.emit(
                DiagBuilder2::bug(format!(
                    "code generation for {} not implemented",
                    hir.desc_full()
                ))
                .span(hir.human_span()),
            );
            return Err(());
        }
    }
    Ok(module)
}

fn codegen_module<'gcx>(
    _cx: Context<'gcx>,
    hir: &hir::Module,
    into: &mut llhd::Module,
) -> Result<llhd::ValueRef> {
    let ent = llhd::Entity::new(hir.name.value.into(), llhd::entity_ty(vec![], vec![]));
    Ok(into.add_entity(ent).into())
}
