// Copyright (c) 2017-2018 Fabian Schuiki

//! The VHDL type system.
//!
//! This module implements the VHDL type system in a fairly isolated manner. The
//! intention is to decouple the type logic as far as possible from details
//! about other parts of the compiler.
//!
//! See IEEE 1076-2008 section 5 for all the details.

#![deny(missing_docs)]

mod types;
mod subtypes;
mod marks;
mod arena;
mod range;
mod ints;

pub use self::types::*;
pub use self::subtypes::*;
pub use self::marks::*;
pub use self::arena::*;
pub use self::range::*;
pub use self::ints::*;
