// Copyright (c) 2017 Fabian Schuiki

//! The high-level intermediate representation for SystemVerilog. After name
//! resolution, the AST is lowered into this representation, eliminating a lot
//! of the syntactic sugar represented in the AST, and resolving default and
//! implicit values.

pub mod lowering;
pub mod nodes;

pub use self::nodes::*;
