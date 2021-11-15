// Copyright (c) 2016-2021 Fabian Schuiki

//! An MLIR type.

use crate::crate_prelude::*;

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
