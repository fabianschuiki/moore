// Copyright (c) 2016-2021 Fabian Schuiki

//! An MLIR type.

use crate::crate_prelude::*;
use std::fmt::{Debug, Display};

/// An MLIR type.
#[derive(Clone, Copy)]
pub struct Type(MlirType);

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
