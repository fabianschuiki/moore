// Copyright (c) 2016-2021 Fabian Schuiki

//! A builder for IR operations.

use crate::crate_prelude::*;

/// A builder for MLIR operations.
pub struct Builder {
    /// The surrounding MLIR context.
    pub(crate) cx: Context,
    /// The location to assign to the operations being built.
    pub(crate) loc: Location,
}

impl Builder {
    /// Create a new builder.
    pub fn new(cx: Context) -> Self {
        Self {
            cx,
            loc: Location::unknown(cx),
        }
    }

    /// Set the location assigned to new operations.
    pub fn set_loc(&mut self, loc: Location) {
        self.loc = loc;
    }

    /// Get the current location that is assigned to new operations.
    pub fn loc(&self) -> Location {
        self.loc
    }
}
