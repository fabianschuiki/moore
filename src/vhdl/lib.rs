// Copyright (c) 2017 Fabian Schuiki

//! This crate implements VHDL for the moore compiler.

#[macro_use]
extern crate moore_common;
extern crate rustc_serialize;
extern crate num;
extern crate typed_arena;
extern crate llhd;
#[macro_use]
extern crate lazy_static;
pub extern crate moore_vhdl_syntax as syntax;
// extern crate futures;

// TODO: Merge this into the `extern crate` above.
pub(crate) use moore_common as common;

#[macro_use]
pub mod arenas;
pub mod symtbl;
#[macro_use]
pub mod score;
pub mod hir;
pub mod ty;
pub mod konst;
pub mod codegen;
pub mod defs;
pub mod typeck;
pub mod make_ctx;
pub mod lazy;
pub mod add_ctx;
pub mod term;
pub mod scope;
pub mod builtin;

mod nodes;
