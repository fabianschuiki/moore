// Copyright (c) 2016-2019 Fabian Schuiki

//! This module implements LLHD code generation.

use common::score::Result;
use common::NodeId;
use context::Context;
use llhd;

pub(crate) fn generate_code<'gcx>(_cx: Context<'gcx>, node_id: NodeId) -> Result<llhd::Module> {
    debug!("generate_code({})", node_id);
    let mut module = llhd::Module::new();
    let ent = llhd::Entity::new(
        "no_clue_what_name_to_generate".to_owned(),
        llhd::entity_ty(vec![], vec![]),
    );
    module.add_entity(ent);
    Ok(module)
}
