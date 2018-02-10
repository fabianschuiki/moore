// Copyright (c) 2018 Fabian Schuiki

//! A context within which compiler passes can be described.
//!
//! Create a new `MakeContext` for each node. Then use the context's
//! functions to declare how the different compiler passes of the node
//! are supposed to work.

#[deny(missing_docs)]

// use futures::{self, Future, IntoFuture};

use moore_common::score::{NodeStorage, Result};
use moore_common::source::Span;
use score::ScoreContext;
use typeck::TypeckContext;
use lazy::{LazyNode, LazyPhaseTable};
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

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx, I: Copy> MakeContext<'sbc, 'lazy, 'sb, 'ast, 'ctx, I> {
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
	pub fn lower_to_hir<F,R>(self, f: F)
	where
		F: FnOnce(&ScoreContext<'lazy, 'sb, 'ast, 'ctx>) -> Result<R> + 'sb,
		// LazyHirTable<'ast, 'ctx>: NodeStorage<I, Node=LazyNode<'ctx, R, ScoreContext<'lazy, 'sb, 'ast, 'ctx>>>,
		// R: IntoFuture<Error=()> + 'sb,
		// R::Item: 'ctx,
		// hir::Arenas: Alloc<R::Item>,
		// // R: IntoFuture<Item=<LazyHirTable<'ctx> as NodeStorage<I>>::Node, Error=()>,
		// LazyHirTable<'sb, 'ctx>: LazyTable<'sb, I, Item=&'ctx R::Item>,
		// hir::Arenas: Alloc<<LazyHirTable<'ctx> as NodeStorage<I>>::Node>,
	{
		debugln!("make.hir");
		// let arenas = self.ctx.sb.arenas;
		// let lazy = futures::lazy(f)
		// 	.map(move |v: R::Item| -> &'ctx R::Item { arenas.hir.alloc(v) })
		// 	.shared()
		// 	.map(|v| *v)
		// 	.map_err(|e| *e);
		// // let allocd = lazy.and_then(|h| self.ctx.sb.arenas.hir.alloc(h));
		// // .shared().map(|v| *v).map_err(|_| ());

		// let node = LazyNode::Pending(Box::new(f));
		// self.ctx.lazy_hir_table.borrow_mut().set(self.id, node);
	}

	/// Schedule a callback that type checks the node.
	pub fn typeck<F>(self, f: F)
		where F: FnOnce(&TypeckContext) -> Result<()>
	{
		debugln!("make.typeck");
	}
}
