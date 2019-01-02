// Copyright (c) 2016-2017 Fabian Schuiki

//! This crate implements SystemVerilog for the moore compiler.

extern crate llhd;
extern crate moore_common;
pub extern crate moore_svlog_hir as hir;
pub extern crate moore_svlog_syntax as syntax;
#[macro_use]
extern crate log;

pub(crate) use moore_common as common;

pub use syntax::*;
