use crate::mlir::{self, Context, DialectHandle, OperationExt};
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
    cx: Context,
    loc: MlirLocation,
    name: &'a str,
}

impl<'a> EntityOpBuilder<'a> {
    pub fn new(cx: Context, loc: MlirLocation) -> Self {
        Self { cx, loc, name: "" }
    }

    pub fn with_unknown_location(cx: Context) -> Self {
        Self::new(cx, unsafe { mlirLocationUnknownGet(cx.raw()) })
    }

    pub fn name(&mut self, name: &'a str) -> &mut Self {
        self.name = name;
        self
    }

    pub fn build(&mut self) -> EntityOp {
        let cx = self.cx;
        let mut state = mlir::OperationState::new("llhd.entity", self.loc);

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

// void EntityOp::build(::mlir::OpBuilder &, ::mlir::OperationState &odsState, ::mlir::TypeRange resultTypes, ::mlir::ValueRange operands, ::llvm::ArrayRef<::mlir::NamedAttribute> attributes) {
//   assert(operands.size() == 0u && "mismatched number of parameters");
//   odsState.addOperands(operands);
//   odsState.addAttributes(attributes);
//   for (unsigned i = 0; i != 1; ++i)
//     (void)odsState.addRegion();
//   assert(resultTypes.size() == 0u && "mismatched number of return types");
//   odsState.addTypes(resultTypes);
// }
