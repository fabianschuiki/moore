// Copyright (c) 2016-2019 Fabian Schuiki

use crate::crate_prelude::*;

pub fn type_of<'gcx>(cx: Context<'gcx>, node_id: NodeId) -> Result<Type<'gcx>> {
    debug!("type_of({})", node_id);
    Ok(cx.mkty_void())
}
