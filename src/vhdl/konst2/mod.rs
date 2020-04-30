// Copyright (c) 2016-2020 Fabian Schuiki

//! This module implements constant values for VHDL.

#![deny(missing_docs)]

mod arena;
mod floating;
mod integer;
mod traits;

pub use self::arena::*;
pub use self::floating::*;
pub use self::integer::*;
pub use self::traits::*;
