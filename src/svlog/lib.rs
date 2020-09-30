// Copyright (c) 2016-2020 Fabian Schuiki

//! The SystemVerilog implementation of the moore compiler.
//!
//! This crate implements a query-based compiler for the SystemVerilog language.
//! It strives to be a complete implementation of IEEE 1800-2017, mapping any
//! input source text to the equivalent LLHD code.
//!
//! The implementation uses different representations of the source text for
//! different parts of the compilation. Such a scheme is necessary due to the
//! very messy nature of SystemVerilog, with its strange mixture of static and
//! dynamic typing. Although the compiler uses queries to be able to handle the
//! more involved and loopy dependencies, the representations form a rough chain
//! of processing that each construct flows through (albeit each at its own
//! pace):
//!
//! - **AST**: Abstract Syntax Tree emitted by the parser in the `syntax` crate.
//! - **RST**: Resolved Syntax Tree which has ambiguities in the grammar
//!   resolved. This is possible by building name resolution scopes and defs on
//!   the AST representation, and resolving names to disambiguate things in the
//!   grammar.
//! - **HIR**: The High-level Intermediate Representation, which does things
//!   like taking the list of constructs in a module body and separating them
//!   into lists of declarations, instances, parameters, etc. Also tries to get
//!   rid of syntactic sugar where appropriate. Type-checking is performed on
//!   this representation, and `ParamEnv` is used to represent different
//!   parametrizations of the same HIR module/interface.
//! - **MIR**: The Medium-level Intermediate Representation, which has all
//!   implicit casting operations and parametrizations made explicit and fully
//!   unrolled. At this point most SystemVerilog craziness has been resolved and
//!   the nodes are crisp and have a clean, fully checked type.
//! - **LLHD**: The Low-level Hardware Description, emitted as the final step
//!   during code generation.

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
        if !$lhs.is_identical($rhs) {
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
#[warn(missing_docs)]
pub mod pattern_mapping;
pub mod port_list;
mod port_mapping;
pub mod resolver;
pub mod rst;
#[warn(missing_docs)]
pub mod ty;
pub mod typeck;
pub mod value;

pub use moore_common::{
    name::Name,
    source::{Span, Spanned},
};

/// A general result returned by the queries.
pub type Result<T> = std::result::Result<T, ()>;

pub use crate::{
    codegen::CodeGenerator,
    context::*,
    inst_details::{InstDetails, InstTargetDetails, InstVerbosityVisitor},
    param_env::{
        IntoNodeEnvId, NodeEnvId, ParamEnv, ParamEnvBinding, ParamEnvData, ParamEnvSource,
    },
    port_mapping::{PortMapping, PortMappingSource},
    // resolver::*,
    syntax::*,
};

/// Items commonly used within the crate.
mod crate_prelude {
    #[allow(unused_imports)]
    pub(crate) use crate::{
        ast::{AnyNode, AnyNodeData},
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
        resolver::{Rib, RibKind},
        ty, typeck, value, IntoNodeEnvId, NodeEnvId, Ref, *,
    };
}

/// A node reference.
///
/// This reference is useful when querying the compiler database for information
/// about a node. It compares the reference *by pointer address*, thus allowing
/// for pessimistic compiler queries.
pub struct Ref<'a, T: 'a + ?Sized>(&'a T);

impl<'a, T: ?Sized> Copy for Ref<'a, T> {}

impl<'a, T: ?Sized> Clone for Ref<'a, T> {
    fn clone(&self) -> Self {
        Ref(self.0)
    }
}

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
    use crate::crate_prelude::*;
    #[allow(deprecated)]
    use crate::{
        hir::lowering::*,
        hir::{accessed_nodes, AccessTable},
        inst_details::*,
        mir::lower::assign::mir_assignment_of_procedural_stmt,
        param_env::*,
        pattern_mapping::*,
        port_list::{self, *},
        port_mapping::*,
        resolver::*,
        rst::*,
        ty::UnpackedType,
        typeck::*,
        value::*,
    };
    use std::{
        cell::RefCell,
        collections::{HashMap, HashSet},
        sync::Arc,
    };

    moore_derive::derive_query_db! {
        /// A collection of compiler queries.
    }
}
pub use crate::queries::*;
