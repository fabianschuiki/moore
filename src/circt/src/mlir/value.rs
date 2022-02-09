// Copyright (c) 2016-2021 Fabian Schuiki

//! An MLIR value.

use crate::crate_prelude::*;
use std::fmt::{Debug, Display};

/// An MLIR value.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Value(MlirValue);

impl Value {
    /// Return the type of this value.
    pub fn ty(&self) -> Type {
        Type::from_raw(unsafe { mlirValueGetType(self.raw()) })
    }
}

impl WrapRaw for Value {
    type RawType = MlirValue;
    fn from_raw(raw: MlirValue) -> Self {
        Self(raw)
    }
    fn raw(&self) -> MlirValue {
        self.0
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        unsafe {
            mlirValuePrint(
                self.raw(),
                Some(super::print_formatter_callback),
                f as *const _ as *mut _,
            )
        };
        Ok(())
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}
