// Copyright (c) 2017 Fabian Schuiki

//! This crate implements VHDL for the moore compiler.

#[macro_use]
extern crate lazy_static;
extern crate llhd;
#[macro_use]
pub extern crate moore_common;
pub extern crate moore_vhdl_syntax as syntax;
extern crate num;
extern crate rustc_serialize;
extern crate typed_arena;
// extern crate futures;

// TODO: Merge this into the `extern crate` above.
pub use moore_common as common;

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
pub mod scope2;
pub mod builtin;
pub mod op;
pub mod overload_resolver;
pub mod ty2;
pub mod debug;
pub mod konst2;

mod nodes;
