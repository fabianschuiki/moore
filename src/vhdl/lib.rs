// Copyright (c) 2017 Fabian Schuiki

//! This crate implements VHDL for the moore compiler.

#[macro_use]
extern crate moore_common;
extern crate rustc_serialize;
extern crate num;
extern crate typed_arena;
pub extern crate moore_vhdl_syntax;

pub use moore_vhdl_syntax as syntax;
pub mod symtbl;
pub mod pass;
pub mod score;
pub mod hir;
