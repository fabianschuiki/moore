// Copyright (c) 2017-2018 Fabian Schuiki

//! The VHDL type system.
//!
//! This module implements the VHDL type system in a fairly isolated manner. The
//! intention is to decouple the type logic as far as possible from details
//! about other parts of the compiler.
//!
//! See IEEE 1076-2008 section 5 for all the details.

#![deny(missing_docs)]

mod access;
mod arena;
mod enums;
mod floats;
mod ints;
mod marks;
mod physical;
mod prelude;
mod range;
mod subtypes;
mod types;

pub use self::access::*;
pub use self::arena::*;
pub use self::enums::*;
pub use self::floats::*;
pub use self::ints::*;
pub use self::marks::*;
pub use self::physical::*;
pub use self::range::*;
pub use self::subtypes::*;
pub use self::types::*;
