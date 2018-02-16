// Copyright (c) 2018 Fabian Schuiki

//! A context within which compiler passes can be described.
//!
//! Create a new `MakeContext` for each node. Then use the context's
//! functions to declare how the different compiler passes of the node
//! are supposed to work.

#[deny(missing_docs)]

use moore_common::NodeId;
use moore_common::score::{NodeStorage, Result};
use moore_common::source::Span;
use score::ScoreContext;
use typeck::TypeckContext;
use lazy::{LazyNode, LazyPhaseTable, LazyHirTable, LazyTypeckTable};
use hir::{self, Alloc};

/// A context within which compiler passes can be described.
///
/// See the module documentation for details.
#[derive(Copy, Clone)]
pub struct MakeContext<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb, I: Copy> {
	/// The outer context.
	pub ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>,
	/// The span of the node in the source code.
	pub span: Span,
	/// The ID of the node being constructed.
	pub id: I,
}

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx, I> MakeContext<'sbc, 'lazy, 'sb, 'ast, 'ctx, I>
	where I: Copy + Into<NodeId>
{
	/// Create a new context.
	pub fn new(ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>, span: Span, id: I) -> MakeContext<'sbc, 'lazy, 'sb, 'ast, 'ctx, I> {
		MakeContext {
			ctx: ctx,
			span: span,
			id: id,
		}
	}

	/// Finalize the description and return the node Id.
	///
	/// This should be the very last step.
	pub fn finish(self) -> I {
		self.id
	}

	/// Schedule a callback that lowers the node to HIR.
	pub fn lower_to_hir<F>(self, f: F)
	where
		LazyHirTable<'sb, 'ast, 'ctx>: NodeStorage<I, Node=LazyNode<F>>,
	{
		debugln!("make.hir");
		self.ctx.lazy.hir.schedule(self.id, f);
	}

	/// Schedule a callback that type checks the node.
	pub fn typeck(self, f: Box<for<'a,'b,'c> Fn(&'a TypeckContext<'b, 'c, 'sb, 'ast, 'ctx>) -> Result<()> + 'sb>) {
		debugln!("make.typeck");
		self.ctx.lazy.typeck.borrow_mut().insert(self.id.into(), LazyNode::Pending(f));
	}
}
