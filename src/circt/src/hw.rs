// Copyright (c) 2016-2021 Fabian Schuiki

use crate::crate_prelude::*;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { circt_sys::mlirGetDialectHandle__hw__() })
}

/// Check if a type is an HW array type.
pub fn is_array_type(ty: Type) -> bool {
    unsafe { hwTypeIsAArrayType(ty.raw()) }
}

/// Create a new array type.
pub fn get_array_type(element: Type, size: usize) -> Type {
    Type::from_raw(unsafe { hwArrayTypeGet(element.raw(), size as _) })
}

/// Get the element type of an array type.
pub fn array_type_element(ty: Type) -> Type {
    Type::from_raw(unsafe { hwArrayTypeGetElementType(ty.raw()) })
}

/// Get the size of an array type.
pub fn array_type_size(ty: Type) -> usize {
    unsafe { hwArrayTypeGetSize(ty.raw()) as _ }
}

/// Check if a type is an HW struct type.
pub fn is_struct_type(ty: Type) -> bool {
    unsafe { hwTypeIsAStructType(ty.raw()) }
}

/// Create a new struct type.
pub fn get_struct_type(
    cx: Context,
    fields: impl IntoIterator<Item = (impl AsRef<str>, Type)>,
) -> Type {
    let raw_fields: Vec<_> = fields
        .into_iter()
        .map(|(name, ty)| HWStructFieldInfo {
            name: unsafe { mlirStringRefCreateFromStr(name.as_ref()) },
            type_: ty.raw(),
        })
        .collect();
    Type::from_raw(unsafe { hwStructTypeGet(cx.raw(), raw_fields.len() as _, raw_fields.as_ptr()) })
}

/// Get the number of fields in a struct type.
pub fn struct_type_size(ty: Type) -> usize {
    unsafe { hwStructTypeGetNumFields(ty.raw()) as _ }
}

/// Get a field of a struct type.
pub fn struct_type_field(ty: Type, offset: usize) -> (String, Type) {
    let info = unsafe { hwStructTypeGetFieldNum(ty.raw(), offset as _) };
    (
        unsafe { mlirStringRefToStr(info.name, String::from) },
        Type::from_raw(info.type_),
    )
}

/// Get an iterator over the fields of a struct type.
pub fn struct_type_fields(ty: Type) -> impl Iterator<Item = (String, Type)> {
    (0..struct_type_size(ty)).map(move |i| struct_type_field(ty, i))
}

def_operation_single_result!(ConstantOp, "hw.constant");
def_operation_single_result!(ArrayCreateOp, "hw.array_create");
def_operation_single_result!(StructCreateOp, "hw.struct_create");
def_binary_operation_explicit_result!(ArraySliceOp, "hw.array_slice");
def_operation_single_result!(ArrayConcatOp, "hw.array_concat");
def_operation_single_result!(ArrayGetOp, "hw.array_get");
def_operation_single_result!(StructExtractOp, "hw.struct_extract");
def_operation_single_result!(StructInjectOp, "hw.struct_inject");

impl ConstantOp {
    /// Create a new constant value.
    pub fn new(builder: &mut Builder, width: usize, value: &BigInt) -> ConstantOp {
        builder.build_with(|builder, state| {
            let ty = get_integer_type(builder.cx, width);
            state.add_attribute("value", get_integer_attr(ty, value.to_i64().unwrap()));
            state.add_result(ty);
        })
    }
}

impl ArrayCreateOp {
    /// Create a new array value.
    pub fn new(builder: &mut Builder, ty: Type, values: impl IntoIterator<Item = Value>) -> Self {
        builder.build_with(move |_, state| {
            for value in values {
                state.add_operand(value);
            }
            state.add_result(ty);
        })
    }
}

impl StructCreateOp {
    /// Create a new struct value.
    pub fn new(builder: &mut Builder, ty: Type, values: impl IntoIterator<Item = Value>) -> Self {
        builder.build_with(move |_, state| {
            for value in values {
                state.add_operand(value);
            }
            state.add_result(ty);
        })
    }
}

impl ArraySliceOp {
    pub fn with_sizes(builder: &mut Builder, value: Value, offset: Value, length: usize) -> Self {
        Self::new(
            builder,
            get_array_type(array_type_element(value.ty()), length),
            value,
            offset,
        )
    }

    pub fn with_const_offset(
        builder: &mut Builder,
        value: Value,
        offset: usize,
        length: usize,
    ) -> Self {
        let offset = crate::hw::ConstantOp::new(builder, 64, &offset.into()).into();
        Self::with_sizes(builder, value, offset, length)
    }
}

impl ArrayConcatOp {
    pub fn new(builder: &mut Builder, values: impl IntoIterator<Item = Value>) -> Self {
        builder.build_with(|_, state| {
            let mut width = 0;
            let mut element_ty = None;
            for value in values {
                state.add_operand(value);
                let ty = value.ty();
                width += array_type_size(ty);
                element_ty = Some(array_type_element(ty));
            }
            state.add_result(get_array_type(element_ty.unwrap(), width));
        })
    }
}

impl ArrayGetOp {
    pub fn new(builder: &mut Builder, value: Value, offset: Value) -> Self {
        builder.build_with(|_, state| {
            state.add_operand(value);
            state.add_operand(offset);
            state.add_result(array_type_element(value.ty()));
        })
    }

    pub fn with_const_offset(builder: &mut Builder, value: Value, offset: usize) -> Self {
        let offset = crate::hw::ConstantOp::new(builder, 64, &offset.into()).into();
        Self::new(builder, value, offset)
    }
}

impl StructExtractOp {
    pub fn new(builder: &mut Builder, value: Value, offset: usize) -> Self {
        builder.build_with(|builder, state| {
            state.add_operand(value);
            let (field_name, field_ty) = struct_type_field(value.ty(), offset);
            state.add_attribute("field", get_string_attr(builder.cx, &field_name));
            state.add_result(field_ty);
        })
    }
}

impl StructInjectOp {
    pub fn new(builder: &mut Builder, value: Value, field_value: Value, offset: usize) -> Self {
        builder.build_with(|builder, state| {
            state.add_operand(value);
            state.add_operand(field_value);
            let (field_name, _) = struct_type_field(value.ty(), offset);
            state.add_attribute("field", get_string_attr(builder.cx, &field_name));
            state.add_result(value.ty());
        })
    }
}
