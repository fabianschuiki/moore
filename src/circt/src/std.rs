// Copyright (c) 2016-2021 Fabian Schuiki

use crate::crate_prelude::*;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { mlirGetDialectHandle__std__() })
}

def_operation!(BranchOp, "std.br");
def_operation!(CondBranchOp, "std.cond_br");
def_operation!(CallOp, "std.call");
def_operation!(ReturnOp, "std.return");

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

impl CallOp {
    /// Create a new call.
    pub fn new(
        builder: &mut Builder,
        callee: &str,
        args: impl IntoIterator<Item = Value>,
        results: impl IntoIterator<Item = Type>,
    ) -> Self {
        builder.build_with(|builder, state| {
            let _num_args = args.into_iter().map(|v| state.add_operand(v)).count();
            let _num_results = results.into_iter().map(|v| state.add_result(v)).count();
            state.add_attribute("callee", get_flat_symbol_ref_attr(builder.cx, callee));
        })
    }
}

impl ReturnOp {
    /// Create a new return.
    pub fn new(builder: &mut Builder, values: impl IntoIterator<Item = Value>) -> Self {
        builder.build_with(|_, state| {
            for v in values {
                state.add_operand(v);
            }
        })
    }
}
