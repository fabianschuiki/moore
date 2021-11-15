use crate::mlir::{Context, OperationExt};
use circt_sys::*;

/// An MLIR module.
#[derive(Clone, Copy)]
pub struct ModuleOp(MlirOperation);

impl OperationExt for ModuleOp {
    fn raw_operation(&self) -> MlirOperation {
        self.0
    }
}

impl ModuleOp {
    pub fn new(cx: Context) -> Self {
        unsafe {
            let mut state = mlirOperationStateGet(
                mlirStringRefCreateFromStr("builtin.module"),
                mlirLocationUnknownGet(cx.raw()),
            );
            let region = mlirRegionCreate();
            mlirRegionAppendOwnedBlock(region, mlirBlockCreate(0, std::ptr::null()));
            mlirOperationStateAddOwnedRegions(&mut state, 1, [region].as_ptr());
            Self(mlirOperationCreate(&mut state))
        }
    }
}
