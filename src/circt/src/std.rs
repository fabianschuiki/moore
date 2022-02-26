// Copyright (c) 2016-2021 Fabian Schuiki

use crate::crate_prelude::*;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { mlirGetDialectHandle__std__() })
}

def_operation!(CallOp, "std.call");
def_operation!(ReturnOp, "std.return");

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
