// Copyright (c) 2016-2017 Fabian Schuiki

//! This crate implements SystemVerilog for the moore compiler.

extern crate moore_common;
pub extern crate moore_svlog_syntax;
pub extern crate moore_svlog_hir;
extern crate bincode;
extern crate rustc_serialize;

pub use moore_svlog_syntax::*;
pub use moore_svlog_hir as hir;
