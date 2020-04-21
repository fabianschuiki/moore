// Copyright (c) 2018 Fabian Schuiki

//! A context within which compiler passes can be described.
//!
//! Create a new `MakeContext` for each node. Then use the context's
//! functions to declare how the different compiler passes of the node
//! are supposed to work.

#[deny(missing_docs)]
use std::fmt::Debug;

use crate::arenas::Alloc;
use crate::hir;
use crate::lazy::*;
use crate::score::{HirTable, ScoreContext};
use moore_common::score::NodeStorage;
use moore_common::source::Span;
use moore_common::NodeId;

/// A context within which compiler passes can be described.
///
/// See the module documentation for details.
pub struct MakeContext<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb, I: Copy> {
    /// The outer context.
    pub ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>,
    /// The span of the node in the source code.
    pub span: Span,
    /// The ID of the node being constructed.
    pub id: I,
}

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx, I> MakeContext<'sbc, 'lazy, 'sb, 'ast, 'ctx, I>
where
    I: Copy + Into<NodeId> + Debug,
{
    /// Create a new context.
    pub fn new(
        ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>,
        span: Span,
        id: I,
    ) -> MakeContext<'sbc, 'lazy, 'sb, 'ast, 'ctx, I> {
        debugln!("make {:?} `{}`", id, {
            let mut sp = span;
            let mut shortened = false;
            if sp.end - sp.begin > 32 {
                sp.end = sp.begin + 32;
                shortened = true;
            }
            let mut extract = sp.extract();
            if let Some(pos) = extract.find('\n') {
                extract.truncate(pos);
            } else if shortened {
                extract.push_str("...");
            }
            extract
        });
        ctx.set_span(id, span);
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
    pub fn lower_to_hir<R>(&self, f: LazyHir<'sb, 'ast, 'ctx, R>)
    where
        LazyHirTable<'sb, 'ast, 'ctx>: NodeStorage<I, Node = LazyNode<LazyHir<'sb, 'ast, 'ctx, R>>>,
    {
        self.ctx
            .lazy
            .hir
            .table
            .borrow_mut()
            .set(self.id, LazyNode::Pending(f));
    }

    /// Store a preconstructed HIR for the node.
    pub fn set_hir<T>(&self, hir: T)
    where
        T: 'ctx,
        HirTable<'ctx>: NodeStorage<I, Node = &'ctx T>,
        hir::Arenas: Alloc<'ctx, 'ctx, T>,
    {
        self.ctx.set_hir(self.id, self.ctx.sb.arenas.hir.alloc(hir));
    }

    /// Schedule a callback that type checks the node.
    pub fn typeck(&self, f: LazyTypeck<'sb, 'ast, 'ctx>) {
        self.ctx
            .lazy
            .typeck
            .borrow_mut()
            .insert(self.id.into(), LazyNode::Pending(f));
    }

    /// Schedule a callback that evaluates the type of the node.
    pub fn typeval(&self, f: LazyTypeval<'sb, 'ast, 'ctx>) {
        self.ctx
            .lazy
            .typeval
            .borrow_mut()
            .insert(self.id.into(), LazyNode::Pending(f));
    }
}
