// Copyright (c) 2018 Fabian Schuiki

//! A context within which nodes can be added.
//!
//! Create a new `AddContext` for groups of nodes that share common information,
//! for example their containing scope. Then use the context's functions to add
//! specific types of nodes, which schedules the necessary work in the lazy
//! tables.

#![deny(missing_docs)]

use crate::common::errors::*;
use crate::common::score::{NodeRef, Result};
use crate::common::source::{Span, INVALID_SPAN};
use crate::common::util::{HasDesc, HasSpan};
use crate::make_ctx::MakeContext;
use crate::score::ScopeRef;
use crate::score::ScoreContext;

/// A context within which nodes can be added.
///
/// See the module documentation for details.
#[derive(Copy, Clone)]
pub struct AddContext<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb> {
    /// The outer context.
    pub ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>,
    /// The scope to which items will be added.
    pub scope: ScopeRef,
}

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Create a new context.
    pub fn new(
        ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>,
        scope: ScopeRef,
    ) -> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
        AddContext {
            ctx: ctx,
            scope: scope,
        }
    }

    /// Create a new context with different scope.
    pub fn with_scope(&self, scope: ScopeRef) -> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
        AddContext {
            scope: scope,
            ..*self
        }
    }

    /// Create a new context for describing a node.
    pub fn make<I>(&self, span: Span) -> (MakeContext<'sbc, 'lazy, 'sb, 'ast, 'ctx, I>, I, ScopeRef)
    where
        I: NodeRef,
    {
        assert!(span != INVALID_SPAN);
        let id = I::alloc();
        (MakeContext::new(self.ctx, span, id), id, self.scope)
    }

    /// Emit a diagnostic that a node is not implemented.
    pub fn unimp<T, R>(&self, node: &T) -> Result<R>
    where
        T: HasSpan + HasDesc,
    {
        self.emit(
            DiagBuilder2::bug(format!("{} not implemented", node.desc())).span(node.human_span()),
        );
        Err(())
    }

    /// Add an optional node.
    ///
    /// This convenience function performs a few things at a time. First it
    /// applies a closure `f` to the value of an option, returning an error if
    /// the closure returns one. Otherwise it wraps the result in an option and
    /// returns it.
    pub fn add_optional<T, F, R>(&self, node: &'ast Option<T>, f: F) -> Result<Option<R>>
    where
        F: FnOnce(&Self, &'ast T) -> Result<R>,
    {
        Ok(match *node {
            Some(ref ast) => Some(f(self, ast)?),
            None => None,
        })
    }
}

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> DiagEmitter for AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    fn emit(&self, diag: DiagBuilder2) {
        self.ctx.emit(diag)
    }
}
