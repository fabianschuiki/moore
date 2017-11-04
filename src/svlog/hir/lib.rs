// Copyright (c) 2017 Fabian Schuiki

//! The high-level intermediate representation for SystemVerilog. After name
//! resolution, the AST is lowered into this representation, eliminating a lot
//! of the syntactic sugar represented in the AST, and resolving default and
//! implicit values.

#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(dead_code)]

extern crate moore_common;
extern crate moore_svlog_syntax;

mod nodes;
mod lower;

pub use self::nodes::*;
pub use self::lower::*;
