// Copyright (c) 2016-2021 Fabian Schuiki

//! Facilities to deal with MLIR attributes.

use crate::crate_prelude::*;
use std::fmt::{Debug, Display};

/// An MLIR attribute.
#[derive(Clone, Copy)]
pub struct Attribute(MlirAttribute);

impl Attribute {
    /// Get the attribute's MLIR context.
    pub fn context(&self) -> Context {
        Context::from_raw(unsafe { mlirAttributeGetContext(self.raw()) })
    }

    /// Associate a name with this attribute.
    pub fn named(&self, name: &str) -> MlirNamedAttribute {
        unsafe { mlirNamedAttributeGet(self.context().get_identifier(name), self.raw()) }
    }
}

impl WrapRaw for Attribute {
    type RawType = MlirAttribute;
    fn from_raw(raw: MlirAttribute) -> Self {
        Self(raw)
    }
    fn raw(&self) -> MlirAttribute {
        self.0
    }
}

impl Display for Attribute {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        unsafe {
            mlirAttributePrint(
                self.raw(),
                Some(super::print_formatter_callback),
                f as *const _ as *mut _,
            )
        };
        Ok(())
    }
}

impl Debug for Attribute {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// Create a new integer attribute.
pub fn get_integer_attr_big(ty: Type, value: &BigInt) -> Attribute {
    if let Some(small_value) = value.to_i64() {
        get_integer_attr(ty, small_value)
    } else {
        Attribute::from_raw(unsafe {
            mlirIntegerAttrGetFromString(ty.raw(), mlirStringRefCreateFromStr(&value.to_string()))
        })
    }
}

/// Create a new unit attribute.
pub fn get_unit_attr(cx: Context) -> Attribute {
    Attribute::from_raw(unsafe { mlirUnitAttrGet(cx.raw()) })
}

/// Create a new integer attribute from an i64 value.
pub fn get_integer_attr(ty: Type, value: i64) -> Attribute {
    Attribute::from_raw(unsafe { mlirIntegerAttrGet(ty.raw(), value) })
}

/// Create a new string attribute.
pub fn get_string_attr(cx: Context, value: &str) -> Attribute {
    Attribute::from_raw(unsafe { mlirStringAttrGet(cx.raw(), mlirStringRefCreateFromStr(value)) })
}

/// Create a new type attribute.
pub fn get_type_attr(value: Type) -> Attribute {
    Attribute::from_raw(unsafe { mlirTypeAttrGet(value.raw()) })
}

/// Create a new flat symbol reference attribute.
pub fn get_flat_symbol_ref_attr(cx: Context, symbol: &str) -> Attribute {
    Attribute::from_raw(unsafe {
        mlirFlatSymbolRefAttrGet(cx.raw(), mlirStringRefCreateFromStr(symbol))
    })
}

/// Create a new array attribute.
pub fn get_array_attr(cx: Context, elements: impl IntoIterator<Item = Attribute>) -> Attribute {
    let elements: Vec<_> = elements.into_iter().map(|x| x.raw()).collect();
    Attribute::from_raw(unsafe {
        mlirArrayAttrGet(cx.raw(), elements.len() as _, elements.as_ptr())
    })
}
