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
            let vector_ty = unsafe {
                mlirVectorTypeGet(1, [3].as_ptr(), get_integer_type(builder.cx, 32).raw())
            };
            let vector_attr = Attribute::from_raw(unsafe {
                mlirDenseElementsAttrInt32Get(vector_ty, 3, [1, 0, 0].as_ptr())
            });
            state.add_attribute("operand_segment_sizes", vector_attr);
        })
    }
}
