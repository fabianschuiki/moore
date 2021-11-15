use crate::crate_prelude::*;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { circt_sys::mlirGetDialectHandle__hw__() })
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
