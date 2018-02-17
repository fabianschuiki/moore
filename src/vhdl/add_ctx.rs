// Copyright (c) 2018 Fabian Schuiki

//! A context within which nodes can be added.
//!
//! Create a new `AddContext` for groups of nodes that share common information,
//! for example their containing scope. Then use the context's functions to add
//! specific types of nodes, which schedules the necessary work in the lazy
//! tables.

#![deny(missing_docs)]

use common::source::Span;
use common::score::NodeRef;
use make_ctx::MakeContext;
use score::ScoreContext;
use score::ScopeRef;

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
	pub fn new(ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>, scope: ScopeRef) -> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
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
    pub fn make<I>(&self, span: Span) -> MakeContext<'sbc, 'lazy, 'sb, 'ast, 'ctx, I> where I: NodeRef {
        MakeContext::new(self.ctx, span, I::alloc())
    }
}
