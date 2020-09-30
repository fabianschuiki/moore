// Copyright (c) 2016-2020 Fabian Schuiki

//! The medium-level intermediate representation for SystemVerilog.
//!
//! Represents a fully typed SystemVerilog design with all implicit operations
//! converted into explicit nodes.

#![deny(missing_docs)]

mod assign;
pub mod lower;
mod lvalue;
mod rvalue;

pub use assign::*;
pub use lvalue::*;
pub use rvalue::*;

mod visit;

pub use visit::*;
