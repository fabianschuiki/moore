// Copyright (c) 2016-2021 Fabian Schuiki

use crate::crate_prelude::*;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { mlirGetDialectHandle__std__() })
}

def_operation!(BranchOp, "std.br");
def_operation!(CondBranchOp, "std.cond_br");

impl BranchOp {
    /// Create a new branch.
    pub fn new(builder: &mut Builder, dest: MlirBlock) -> Self {
        builder.build_with(|_, state| {
            state.add_successor(dest);
        })
    }
}

impl CondBranchOp {
    /// Create a new conditional branch.
    pub fn new(
        builder: &mut Builder,
        condition: Value,
        true_dest: MlirBlock,
        false_dest: MlirBlock,
    ) -> Self {
        builder.build_with(|_, state| {
            state.add_operand(condition);
            state.add_successor(true_dest);
            state.add_successor(false_dest);
        })
    }
}
