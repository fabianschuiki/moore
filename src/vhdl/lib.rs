// Copyright (c) 2016-2020 Fabian Schuiki

//! This crate implements VHDL for the moore compiler.

#![allow(bare_trait_objects)] // Remove this once fixed
#![allow(unused_doc_comments)] // Remove this once fixed

#[macro_use]
extern crate lazy_static;
extern crate llhd;
#[macro_use]
pub extern crate moore_common;
pub extern crate moore_vhdl_syntax as syntax;
extern crate num;
extern crate typed_arena;
// extern crate futures;

// TODO: Merge this into the `extern crate` above.
pub use moore_common as common;

#[macro_use]
pub mod arenas;
pub mod symtbl;
#[macro_use]
pub mod score;
pub mod add_ctx;
pub mod builtin;
pub mod codegen;
pub mod debug;
pub mod defs;
pub mod hir;
pub mod konst;
pub mod konst2;
pub mod lazy;
pub mod make_ctx;
pub mod op;
pub mod overload_resolver;
pub mod scope;
pub mod scope2;
pub mod term;
pub mod ty;
pub mod ty2;
pub mod typeck;

mod nodes;
