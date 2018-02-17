// Copyright (c) 2018 Fabian Schuiki

//! Expressions

#![deny(missing_docs)]

use common::errors::*;
use common::source::Spanned;
use common::score::Result;
use add_ctx::AddContext;
use syntax::ast;
use score::*;
use term::TermContext;
use hir;

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Add an expression.
    pub fn add_expr(&self, expr: &'ast ast::Expr) -> Result<ExprRef> {
        self.emit(DiagBuilder2::bug("expressions not implemented").span(expr.span));
        Err(())
        // let (mk, id, scope) = self.make::<ExprRef>(expr.span);
        // mk.lower_to_hir(Box::new(move |sbc|{
        //     let ctx = TermContext::new(sbc, scope);
        //     let term = ctx.termify_expr(expr)?;
        //     ctx.term_to_expr(term)
        // }));
        // Ok(mk.finish())
    }

    /// Add a list of choices.
    pub fn add_choices(&self, _ast: &'ast Vec<ast::Expr>) -> Result<hir::Choices> {
        self.emit(DiagBuilder2::bug("choices not implemented"));
        Err(())
    }

    /// Add a discrete range.
    pub fn add_discrete_range(&self, ast: &'ast ast::Expr) -> Result<Spanned<hir::DiscreteRange>> {
        let ctx = TermContext::new(self.ctx, self.scope);
        let term = ctx.termify_expr(ast)?;
        ctx.term_to_discrete_range(term)
    }
}
