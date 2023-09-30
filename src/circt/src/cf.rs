// Copyright (c) 2016-2021 Fabian Schuiki

use crate::crate_prelude::*;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { mlirGetDialectHandle__cf__() })
}

def_operation!(BranchOp, "cf.br");
def_operation!(CondBranchOp, "cf.cond_br");

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
        builder.build_with(|builder, state| {
            state.add_operand(condition);
            state.add_successor(true_dest);
            state.add_successor(false_dest);
            let dense_array_attr = Attribute::from_raw(unsafe {
                mlirDenseI32ArrayGet(builder.cx.raw(), 3, [1, 0, 0].as_ptr())
            });
            state.add_attribute("operand_segment_sizes", dense_array_attr);
        })
    }
}
