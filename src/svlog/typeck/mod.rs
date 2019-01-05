// Copyright (c) 2016-2019 Fabian Schuiki

use crate::{crate_prelude::*, hir::HirNode};

pub fn type_of<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<Type<'gcx>> {
    let hir = cx.hir_of(node_id)?;

    #[allow(unreachable_patterns)]
    match hir {
        HirNode::Port(_) => Ok(cx.mkty_void()),
        _ => {
            cx.emit(
                DiagBuilder2::bug(format!("type of {} not implemented", hir.desc_full()))
                    .span(hir.human_span()),
            );
            Err(())
        }
    }
}
