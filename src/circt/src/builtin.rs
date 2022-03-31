// Copyright (c) 2016-2021 Fabian Schuiki

use crate::crate_prelude::*;

def_operation!(ModuleOp, "builtin.module");
def_operation!(
    UnrealizedConversionCastOp,
    "builtin.unrealized_conversion_cast"
);

impl ModuleOp {
    /// Create a new module.
    pub fn new(cx: Context) -> Self {
        unsafe {
            let mut state = mlirOperationStateGet(
                mlirStringRefCreateFromStr(Self::operation_name()),
                mlirLocationUnknownGet(cx.raw()),
            );
            let region = mlirRegionCreate();
            mlirRegionAppendOwnedBlock(
                region,
                mlirBlockCreate(0, std::ptr::null(), std::ptr::null()),
            );
            mlirOperationStateAddOwnedRegions(&mut state, 1, [region].as_ptr());
            Self(mlirOperationCreate(&mut state))
        }
    }
}

impl SingleRegionOp for ModuleOp {}
impl SingleBlockOp for ModuleOp {}

impl UnrealizedConversionCastOp {
    /// Create a new unrealized conversion cast operation.
    pub fn new(
        builder: &mut Builder,
        values: impl IntoIterator<Item = Value>,
        result_tys: impl IntoIterator<Item = Type>,
    ) -> Self {
        builder.build_with(|_, state| {
            for value in values {
                state.add_operand(value);
            }
            for rty in result_tys {
                state.add_result(rty);
            }
        })
    }
}
