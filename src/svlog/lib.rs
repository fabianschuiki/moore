// Copyright (c) 2016-2017 Fabian Schuiki

//! This crate implements SystemVerilog for the moore compiler.

extern crate llhd;
#[macro_use]
extern crate moore_common;
pub extern crate moore_svlog_syntax as syntax;
#[macro_use]
extern crate log;

pub(crate) use moore_common as common;

mod ast_map;
pub mod codegen;
mod context;
pub mod hir;
pub mod ty;
pub mod typeck;

pub use crate::context::*;
pub use crate::syntax::*;

/// Items commonly used within the crate.
mod crate_prelude {
    pub use crate::ast;
    pub use crate::common::errors::*;
    pub use crate::common::name::Name;
    pub use crate::common::score::Result;
    pub use crate::common::source::{Span, Spanned};
    pub use crate::common::util::{HasDesc, HasSpan};
    pub use crate::common::NodeId;
    pub use crate::context::Context;
    pub use crate::hir;
    pub use crate::ty::{self, Type};
    pub use crate::typeck;
}
