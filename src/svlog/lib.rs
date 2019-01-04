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
mod codegen;
mod context;
pub mod hir;
pub mod ty;
mod typeck;

pub use crate::context::*;
pub use crate::syntax::*;

/// Items commonly used within the crate.
mod crate_prelude {
    #[allow(unused_imports)]
    pub(crate) use crate::{
        ast,
        common::errors::*,
        common::name::Name,
        common::score::Result,
        common::source::{Span, Spanned},
        common::util::{HasDesc, HasSpan},
        common::NodeId,
        context::{BaseContext, Context, GlobalContext},
        hir,
        ty::{self, Type},
        typeck,
    };
}
