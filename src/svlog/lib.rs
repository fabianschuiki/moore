// Copyright (c) 2016-2019 Fabian Schuiki

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
pub mod mir;
mod param_env;
mod port_mapping;
mod resolver;
pub mod ty;
mod typeck;
pub mod value;

pub use crate::{
    codegen::CodeGenerator,
    context::*,
    param_env::{NodeEnvId, ParamEnv, ParamEnvBinding, ParamEnvData, ParamEnvSource},
    port_mapping::{PortMapping, PortMappingSource},
    resolver::{Rib, RibKind},
    syntax::*,
};

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
        hir, mir, param_env, port_mapping,
        resolver::{self, Rib, RibKind},
        ty, typeck, value, NodeEnvId,
    };
}
