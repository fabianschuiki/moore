// Copyright (c) 2016-2020 Fabian Schuiki

//! This crate implements SystemVerilog for the moore compiler.

#[macro_use]
extern crate moore_common;
#[macro_use]
extern crate log;

pub extern crate moore_svlog_syntax as syntax;
pub(crate) use moore_common as common;

// Inline the salsa crate as a module, since we use a very esoteric branch for
// now.
// TODO(fschuiki): Remove this once salsa is regular dep again
#[macro_use]
mod salsa;

/// Assert that a condition holds, or emit a bug diagnostic and panic.
#[macro_export]
macro_rules! assert_span {
    ($cond:expr, $span:expr, $emitter:expr) => ({
        $crate::assert_span!(@IMPL $cond, $span, $emitter, "assertion failed: {}", stringify!($cond))
    });
    ($cond:expr, $span:expr, $emitter:expr,) => ({
        $crate::assert_span!(@IMPL $cond, $span, $emitter, "assertion failed: {}", stringify!($cond))
    });
    ($cond:expr, $span:expr, $emitter:expr, $($arg:tt)+) => ({
        $crate::assert_span!(@IMPL $cond, $span, $emitter, $($arg)+)
    });
    (@IMPL $cond:expr, $span:expr, $emitter:expr, $($arg:tt)*) => ({
        if !$cond {
            let msg = format!($($arg)*);
            $emitter.emit(
                moore_common::errors::DiagBuilder2::bug(&msg)
                .span($span)
                .add_note(format!("Assertion failed: {}", stringify!($cond)))
                .add_note(format!("Encountered at {}:{}", file!(), line!()))
            );
            panic!("{}", msg);
        }
    });
}

/// Emit a bug diagnostic and panic.
#[macro_export]
macro_rules! bug_span {
    ($span:expr, $emitter:expr, $($arg:tt)+) => ({
        let msg = format!($($arg)*);
        $emitter.emit(
            moore_common::errors::DiagBuilder2::bug(&msg)
            .span($span)
            .add_note(format!("Encountered at {}:{}", file!(), line!()))
        );
        panic!("{}", msg);
    });
}

/// Assert that two types are identical, or emit a bug diagnostic and panic.
#[macro_export]
macro_rules! assert_type {
    ($lhs:expr, $rhs:expr, $span:expr, $emitter:expr) => ({
        $crate::assert_type!($lhs, $rhs, $span, $emitter,)
    });
    ($lhs:expr, $rhs:expr, $span:expr, $emitter:expr,) => ({
        $crate::assert_type!($lhs, $rhs, $span, $emitter, "type assertion failed: `{}` != `{}`", $lhs, $rhs)
    });
    ($lhs:expr, $rhs:expr, $span:expr, $emitter:expr, $($arg:tt)+) => ({
        if !$crate::ty::identical($lhs, $rhs) {
            let msg = format!($($arg)*);
            $emitter.emit(
                moore_common::errors::DiagBuilder2::bug(&msg)
                .span($span)
                .add_note("Type mismatch:")
                .add_note(format!("    Left-hand side:  `{}`", $lhs))
                .add_note(format!("    Right-hand side: `{}`", $rhs))
                .add_note(format!("Encountered at {}:{}", file!(), line!()))
            );
            panic!("{}", msg);
        }
    });
}

mod ast_map;
mod codegen;
mod context;
pub mod hir;
pub mod mir;
mod param_env;
mod port_mapping;
mod resolver;
pub mod ty;
pub mod typeck;
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
        common::{
            errors::*,
            name::Name,
            score::Result,
            source::{Span, Spanned},
            util::{HasDesc, HasSpan},
            NodeId, SessionContext, Verbosity,
        },
        context::{BaseContext, Context, GlobalContext},
        hir, mir, param_env, port_mapping,
        resolver::{self, Rib, RibKind},
        ty, typeck, value, NodeEnvId,
    };
}
