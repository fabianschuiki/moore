use crate::crate_prelude::*;
use crate::mlir::{self, DialectHandle};
use circt_sys::*;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { circt_sys::mlirGetDialectHandle__llhd__() })
}

/// An LLHD entity.
#[derive(Clone, Copy)]
pub struct EntityOp(MlirOperation);

impl OperationExt for EntityOp {
    fn raw_operation(&self) -> MlirOperation {
        self.0
    }
}

pub struct EntityOpBuilder<'a> {
    builder: &'a mut Builder,
    name: &'a str,
}

impl<'a> EntityOpBuilder<'a> {
    pub fn new(builder: &'a mut Builder) -> Self {
        Self { builder, name: "" }
    }

    pub fn name(&mut self, name: &'a str) -> &mut Self {
        self.name = name;
        self
    }

    pub fn build(&mut self) -> EntityOp {
        let cx = self.builder.cx;
        let mut state = mlir::OperationState::new("llhd.entity", self.builder.loc.raw());

        unsafe {
            let sym_name_ident =
                mlirIdentifierGet(cx.raw(), mlirStringRefCreateFromStr("sym_name"));
            let sym_name_attr = mlirNamedAttributeGet(
                sym_name_ident,
                mlirStringAttrGet(cx.raw(), mlirStringRefCreateFromStr(self.name)),
            );
            let type_ident = mlirIdentifierGet(cx.raw(), mlirStringRefCreateFromStr("type"));
            let type_attr = mlirNamedAttributeGet(
                type_ident,
                mlirTypeAttrGet(mlirFunctionTypeGet(
                    cx.raw(),
                    0,
                    std::ptr::null(),
                    0,
                    std::ptr::null(),
                )),
            );
            let ins_ident = mlirIdentifierGet(cx.raw(), mlirStringRefCreateFromStr("ins"));
            let ins_attr = mlirNamedAttributeGet(
                ins_ident,
                mlirIntegerAttrGet(mlirIntegerTypeGet(cx.raw(), 64), 0),
            );
            mlirOperationStateAddAttributes(
                state.raw_mut(),
                3,
                [sym_name_attr, type_attr, ins_attr].as_ptr(),
            );

            let region = mlirRegionCreate();
            mlirRegionAppendOwnedBlock(region, mlirBlockCreate(0, std::ptr::null()));
            mlirOperationStateAddOwnedRegions(state.raw_mut(), 1, [region].as_ptr());
        }

        EntityOp(state.build().raw_operation())
    }
}
