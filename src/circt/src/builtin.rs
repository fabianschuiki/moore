use crate::crate_prelude::*;

def_operation!(ModuleOp, "builtin.module");

impl ModuleOp {
    pub fn new(cx: Context) -> Self {
        unsafe {
            let mut state = mlirOperationStateGet(
                mlirStringRefCreateFromStr(Self::operation_name()),
                mlirLocationUnknownGet(cx.raw()),
            );
            let region = mlirRegionCreate();
            mlirRegionAppendOwnedBlock(region, mlirBlockCreate(0, std::ptr::null()));
            mlirOperationStateAddOwnedRegions(&mut state, 1, [region].as_ptr());
            Self(mlirOperationCreate(&mut state))
        }
    }
}
