// Copyright (c) 2016-2021 Fabian Schuiki

//! MLIR source locations.

use crate::crate_prelude::*;

/// An MLIR source location.
#[derive(Clone, Copy)]
pub struct Location(MlirLocation);

impl Location {
    /// Create a new unknown source location.
    pub fn unknown(cx: Context) -> Self {
        Location(unsafe { mlirLocationUnknownGet(cx.raw()) })
    }

    /// Create a new location from a file, line, and column.
    pub fn file_line_col(cx: Context, filename: &str, line: usize, col: usize) -> Self {
        Location(unsafe {
            mlirLocationFileLineColGet(
                cx.raw(),
                mlirStringRefCreateFromStr(filename),
                line as _,
                col as _,
            )
        })
    }
}

impl WrapRaw for Location {
    type RawType = MlirLocation;
    fn from_raw(raw: MlirLocation) -> Self {
        Self(raw)
    }
    fn raw(&self) -> MlirLocation {
        self.0
    }
}
