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
    inputs: Vec<MlirType>,
    outputs: Vec<MlirType>,
}

impl<'a> EntityOpBuilder<'a> {
    pub fn new(builder: &'a mut Builder) -> Self {
        Self {
            builder,
            name: "",
            inputs: vec![],
            outputs: vec![],
        }
    }

    /// Set the entity name.
    pub fn name(&mut self, name: &'a str) -> &mut Self {
        self.name = name;
        self
    }

    /// Add an input port.
    pub fn add_input(&mut self) -> &mut Self {
        self.inputs
            .push(unsafe { mlirIntegerTypeGet(self.builder.cx.raw(), 42) });
        self
    }

    /// Add an output port.
    pub fn add_output(&mut self) -> &mut Self {
        self.outputs
            .push(unsafe { mlirIntegerTypeGet(self.builder.cx.raw(), 43) });
        self
    }

    pub fn build(&mut self) -> EntityOp {
        let cx = self.builder.cx;
        let mut state = mlir::OperationState::new("llhd.entity", self.builder.loc.raw());
        let types: Vec<MlirType> = self
            .inputs
            .iter()
            .chain(self.outputs.iter())
            .copied()
            .collect();

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
                    types.len() as _,
                    types.as_ptr(),
                    0,
                    std::ptr::null(),
                )),
            );
            let ins_ident = mlirIdentifierGet(cx.raw(), mlirStringRefCreateFromStr("ins"));
            let ins_attr = mlirNamedAttributeGet(
                ins_ident,
                mlirIntegerAttrGet(mlirIntegerTypeGet(cx.raw(), 64), self.inputs.len() as _),
            );
            mlirOperationStateAddAttributes(
                state.raw_mut(),
                3,
                [sym_name_attr, type_attr, ins_attr].as_ptr(),
            );

            let region = mlirRegionCreate();
            mlirRegionAppendOwnedBlock(region, mlirBlockCreate(types.len() as _, types.as_ptr()));
            mlirOperationStateAddOwnedRegions(state.raw_mut(), 1, [region].as_ptr());
        }

        EntityOp(state.build().raw_operation())
    }
}
