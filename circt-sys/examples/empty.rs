extern crate circt_sys as circt;
use circt::*;

fn main() {
    unsafe { magic() }
}

unsafe fn magic() {
    let cx = mlirContextCreate();
    mlirDialectHandleLoadDialect(mlirGetDialectHandle__hw__(), cx);

    // Create a root MLIR `ModuleOp`.
    let module = {
        let mut module = mlirOperationStateGet(
            mlirStringRefCreateFromStr("module"),
            mlirLocationUnknownGet(cx),
        );
        let region = mlirRegionCreate();
        mlirRegionAppendOwnedBlock(region, mlirBlockCreate(0, std::ptr::null()));
        mlirOperationStateAddOwnedRegions(&mut module, 1, [region].as_ptr());
        mlirOperationCreate(&mut module)
    };

    // Create a dummy "hw.module" op.
    let mut hw_module = mlirOperationStateGet(
        mlirStringRefCreateFromStr("hw.module"),
        mlirLocationUnknownGet(cx),
    );
    let sym_name_ident = mlirIdentifierGet(cx, mlirStringRefCreateFromStr("sym_name"));
    let sym_name_attr = mlirNamedAttributeGet(
        sym_name_ident,
        mlirStringAttrGet(cx, mlirStringRefCreateFromStr("Foo")),
    );
    let type_ident = mlirIdentifierGet(cx, mlirStringRefCreateFromStr("type"));
    let type_attr = mlirNamedAttributeGet(
        type_ident,
        mlirTypeAttrGet(mlirFunctionTypeGet(
            cx,
            0,
            std::ptr::null(),
            0,
            std::ptr::null(),
        )),
    );
    mlirOperationStateAddAttributes(&mut hw_module, 2, [sym_name_attr, type_attr].as_ptr());

    let block = mlirBlockCreate(0, std::ptr::null());
    let region = mlirRegionCreate();
    mlirRegionAppendOwnedBlock(region, block);
    mlirOperationStateAddOwnedRegions(&mut hw_module, 1, [region].as_ptr());

    let hw_module = mlirOperationCreate(&mut hw_module);
    mlirBlockInsertOwnedOperationBefore(
        mlirRegionGetFirstBlock(mlirOperationGetRegion(module, 0)),
        MlirOperation {
            ptr: std::ptr::null_mut(),
        },
        hw_module,
    );

    mlirOperationDump(module);
    mlirContextDestroy(cx);
}
