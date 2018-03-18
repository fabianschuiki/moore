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

pub use self::types::*;
