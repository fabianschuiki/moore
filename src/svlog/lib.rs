// Copyright (c) 2016-2017 Fabian Schuiki

//! This crate implements SystemVerilog for the moore compiler.

extern crate llhd;
extern crate moore_common;
pub extern crate moore_svlog_syntax as syntax;
#[macro_use]
extern crate log;

pub(crate) use moore_common as common;

mod ast_map;
pub mod codegen;
mod context;
pub mod hir;

pub use context::*;
pub use syntax::*;

/// Items commonly used within the crate.
mod crate_prelude {
    pub use ast;
    pub use common::errors::*;
    pub use common::score::Result;
    pub use common::util::{HasDesc, HasSpan};
    pub use common::NodeId;
    pub use context::Context;
}
