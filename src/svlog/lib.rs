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
mod inst_details;
pub mod mir;
mod param_env;
mod port_mapping;
mod resolver;
pub mod ty;
pub mod typeck;
pub mod value;

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

pub use crate::{
    codegen::CodeGenerator,
    context::*,
    inst_details::{InstDetails, InstTargetDetails, InstVerbosityVisitor},
    param_env::{
        IntoNodeEnvId, NodeEnvId, ParamEnv, ParamEnvBinding, ParamEnvData, ParamEnvSource,
    },
    port_mapping::{PortMapping, PortMappingSource},
    resolver::*,
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
        ty, typeck, value, IntoNodeEnvId, NodeEnvId, Ref,
    };
}

/// A node reference.
///
/// This reference is useful when querying the compiler database for information
/// about a node. It compares the reference *by pointer address*, thus allowing
/// for pessimistic compiler queries.
#[derive(Copy, Clone)]
pub struct Ref<'a, T: 'a + ?Sized>(&'a T);

impl<'a, T: ?Sized> From<&'a T> for Ref<'a, T> {
    fn from(r: &'a T) -> Ref<'a, T> {
        Ref(r)
    }
}

impl<'a, T: ?Sized> std::ops::Deref for Ref<'a, T> {
    type Target = &'a T;

    fn deref(&self) -> &&'a T {
        &self.0
    }
}

impl<T: ?Sized> Eq for Ref<'_, T> {}

impl<T: ?Sized> PartialEq for Ref<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl<T: ?Sized> std::hash::Hash for Ref<'_, T> {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        std::ptr::hash(self.0, h)
    }
}

impl<T: ?Sized> std::fmt::Debug for Ref<'_, T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.0, f)
    }
}

impl<T: ?Sized> std::fmt::Display for Ref<'_, T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Display::fmt(self.0, f)
    }
}

impl<T: ?Sized> std::fmt::Binary for Ref<'_, T>
where
    T: std::fmt::Binary,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Binary::fmt(self.0, f)
    }
}

/// A few checks to ensure that `Ref` can be passed around properly.
#[allow(dead_code, unused_variables)]
mod checks {
    use super::*;

    trait Dummy {}
    struct Foo;
    impl Dummy for Foo {}

    fn checks1<'a>(x: Ref<'a, impl Dummy>) {}
    fn checks2<'a>(x: Ref<'a, dyn Dummy>) {}

    fn checks3() {
        let foo = Foo;
        checks1(Ref(&foo));
        checks2(Ref(&foo));
    }

    fn checks4<'a>(x: Ref<'a, impl Dummy>) {
        checks2(Ref(*x));
    }

    fn checks5<'a>(x: Ref<'a, dyn Dummy>) {
        checks2(Ref(*x));
    }
}

// Derive the database queries. We group this into a module such that we can
// selectively enable/disable trace messages using `moore_svlog::queries` in the
// `MOORE_LOG` env var.
mod queries {
    use super::*;
    moore_derive::derive_query_db! {
        /// A collection of compiler queries.
    }
}
pub use crate::queries::*;
