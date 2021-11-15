// Copyright (c) 2016-2021 Fabian Schuiki

//! An MLIR type.

use crate::crate_prelude::*;
use std::fmt::{Debug, Display};

/// An MLIR type.
#[derive(Clone, Copy)]
pub struct Type(MlirType);

impl Type {
    /// Get the type's MLIR context.
    pub fn context(&self) -> Context {
        Context::from_raw(unsafe { mlirTypeGetContext(self.raw()) })
    }
}

impl WrapRaw for Type {
    type RawType = MlirType;
    fn from_raw(raw: MlirType) -> Self {
        Self(raw)
    }
    fn raw(&self) -> MlirType {
        self.0
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        unsafe {
            mlirTypePrint(
                self.raw(),
                Some(super::print_formatter_callback),
                f as *const _ as *mut _,
            )
        };
        Ok(())
    }
}

impl Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// Create a new integer type of a given width.
pub fn get_integer_type(cx: Context, bitwidth: usize) -> Type {
    Type::from_raw(unsafe { mlirIntegerTypeGet(cx.raw(), bitwidth as _) })
}

/// Return the width of an integer type.
pub fn integer_type_width(ty: Type) -> usize {
    unsafe { mlirIntegerTypeGetWidth(ty.raw()) as _ }
}
