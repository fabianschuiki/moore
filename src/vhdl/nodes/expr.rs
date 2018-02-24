// Copyright (c) 2018 Fabian Schuiki

//! Expressions

use common::errors::*;
use common::source::Spanned;
use common::score::Result;

use add_ctx::AddContext;
use syntax::ast;
use score::*;
use term::TermContext;
use make_ctx::MakeContext;
use hir;
use typeck::TypeckContext;
use ty::*;

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Add an expression.
    pub fn add_expr(&self, expr: &'ast ast::Expr) -> Result<ExprRef> {
        let (mk, _id, scope) = self.make::<ExprRef>(expr.span);
        mk.lower_to_hir(Box::new(move |sbc|{
            let ctx = TermContext::new(sbc, scope);
            let term = ctx.termify_expr(expr)?;
            ctx.term_to_expr_raw(term)
        }));
        self.schedule_expr(&mk);
        Ok(mk.finish())
    }

    /// Add an expression already lowered to HIR.
    pub fn add_expr_hir(&self, hir: hir::Expr) -> Result<ExprRef> {
        let (mk, _, _) = self.make::<ExprRef>(hir.span);
        mk.set_hir(hir);
        self.schedule_expr(&mk);
        Ok(mk.finish())
    }

    /// Add an expression term.
    pub fn schedule_expr(&self, mk: &MakeContext<ExprRef>) {
        let id = mk.id;
        mk.typeval(Box::new(move |tyc|{
            let hir = tyc.ctx.lazy_hir(id)?;
            let tyctx = tyc.ctx.type_context(id);
            typeval_expr(tyc, id, hir, tyctx)
        }));
    }

    /// Add a list of choices.
    pub fn add_choices<I>(
        &self,
        ast: Spanned<I>
    ) -> Result<Spanned<hir::Choices>>
        where I: IntoIterator<Item=&'ast ast::Expr>
    {
        let ctx = TermContext::new(self.ctx, self.scope);
        let choices = ast.value
            .into_iter()
            .map(|ast|{
                let term = ctx.termify_expr(ast)?;
                ctx.term_to_choice(term)
            })
            .collect::<Vec<Result<_>>>()
            .into_iter()
            .collect::<Result<Vec<_>>>()?;
        Ok(Spanned::new(choices, ast.span))
    }

    /// Add a discrete range.
    pub fn add_discrete_range(&self, ast: &'ast ast::Expr) -> Result<Spanned<hir::DiscreteRange>> {
        let ctx = TermContext::new(self.ctx, self.scope);
        let term = ctx.termify_expr(ast)?;
        ctx.term_to_discrete_range(term)
    }
}

/// Evaluate the type of an expression.
pub fn typeval_expr<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb>(
    tyc: &TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx>,
    id: ExprRef,
    hir: &hir::Expr,
    tyctx: Option<TypeCtx<'ctx>>,
) -> Result<&'ctx Ty> {
    match hir.data {
        _ => {
            tyc.emit(
                DiagBuilder2::bug(format!("typeval for expression `{}` not implemented", hir.span.extract()))
                .span(hir.span)
            );
            debugln!("It is a {:#?}", hir.data);
            Err(())
        }
    }
}
