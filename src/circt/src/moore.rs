// Copyright (c) 2016-2021 Fabian Schuiki

use crate::crate_prelude::*;

/// Define a shift operation with value and amount operands and a
/// unit attribute indicating whether the shift is arithmetic.
macro_rules! def_shift_operation {
    ($name:ident, $operation_name:expr) => {
        def_operation_single_result!($name, $operation_name);

        impl $name {
            pub fn new(
                builder: &mut Builder,
                value: Value,
                amount: Value,
                arithmetic: bool,
            ) -> Self {
                builder.build_with(|builder, state| {
                    state.add_operand(value);
                    state.add_operand(amount);
                    if arithmetic {
                        state.add_attribute("arithmetic", get_unit_attr(builder.cx));
                    }
                    state.add_result(value.ty());
                })
            }
        }
    };
}

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { mlirGetDialectHandle__moore__() })
}

/// Check if the type is a simple bitvector type.
pub fn is_simple_bitvector_type(ty: Type) -> bool {
    unsafe { mooreIsSimpleBitVectorType(ty.raw()) }
}

/// Get the size of a simple bit-vector in bits.
pub fn get_simple_bitvector_size(ty: Type) -> usize {
    assert!(unsafe { mooreIsSimpleBitVectorType(ty.raw()) });
    unsafe { mooreGetSimpleBitVectorSize(ty.raw()) as usize }
}

/// Check if type is four-valued.
pub fn is_four_valued(ty: Type) -> bool {
    unsafe { mooreIsFourValuedType(ty.raw()) }
}

/// Create a new simple bit-vector type.
pub fn get_simple_bitvector_type(
    cx: Context,
    four_valued: bool,
    signed: bool,
    size: usize,
) -> Type {
    Type::from_raw(unsafe {
        mooreSimpleBitVectorTypeGet(cx.raw(), four_valued, signed, size as u32)
    })
}

def_shift_operation!(ShlOp, "moore.mir.shl");
def_shift_operation!(ShrOp, "moore.mir.shr");
def_operation_single_result!(ConcatOp, "moore.mir.concat");

impl ConcatOp {
    pub fn new(builder: &mut Builder, values: impl IntoIterator<Item = Value>) -> Self {
        builder.build_with(|builder, state| {
            let mut width = 0;
            let mut four_valued = false;
            for value in values {
                state.add_operand(value);
                if is_four_valued(value.ty()) {
                    four_valued = true;
                }
                width += get_simple_bitvector_size(value.ty());
            }
            state.add_result(get_simple_bitvector_type(
                builder.cx,
                four_valued,
                false,
                width,
            ));
        })
    }
}
