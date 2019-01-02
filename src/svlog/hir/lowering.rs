// Copyright (c) 2016-2019 Fabian Schuiki

//! Lowering of AST nodes to HIR nodes.

use common::score::Result;
use common::NodeId;
use context::Context;
use hir::HirNode;

pub(crate) fn hir_of<'gcx>(_cx: Context<'gcx>, node_id: NodeId) -> Result<HirNode> {
    debug!("hir_of({})", node_id);
    unimplemented!()
}
