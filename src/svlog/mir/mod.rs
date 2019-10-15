// Copyright (c) 2017 Fabian Schuiki

//! The medium-level intermediate representation for SystemVerilog.
//!
//! Represents a fully typed SystemVerilog design with all implicit operations
//! converted into explicit nodes.

#![deny(missing_docs)]

pub mod lower;
mod lvalue;
mod rvalue;

pub use lvalue::*;
pub use rvalue::*;
