// Copyright (c) 2018 Fabian Schuiki

//! Miscellaneous nodes

use crate::common::score::Result;
use crate::common::source::Spanned;

use crate::add_ctx::AddContext;
use crate::hir;
use crate::make_ctx::MakeContext;
use crate::score::*;
use crate::syntax::ast;
use crate::term::TermContext;
use crate::ty::*;

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
    /// Add a subtype indication.
    pub fn add_subtype_ind(&self, ind: &'ast ast::SubtypeInd) -> Result<SubtypeIndRef> {
        let (mk, _, scope) = self.make::<SubtypeIndRef>(ind.span);
        mk.lower_to_hir(Box::new(move |sbc| {
            let ctx = TermContext::new(sbc, scope);
            let term = ctx.termify_subtype_ind(ind)?;
            Ok(ctx.term_to_subtype_ind(term)?.value)
        }));
        self.schedule_subtype_ind(&mk);
        Ok(mk.finish())
    }

    /// Add a subtype indication already lowered to HIR.
    pub fn add_subtype_ind_hir(&self, hir: hir::SubtypeInd) -> Result<SubtypeIndRef> {
        let (mk, _, _) = self.make::<SubtypeIndRef>(hir.span);
        mk.set_hir(hir);
        self.schedule_subtype_ind(&mk);
        Ok(mk.finish())
    }

    /// Schedule subtype indication tasks.
    pub fn schedule_subtype_ind(&self, mk: &MakeContext<SubtypeIndRef>) {
        let id = mk.id;
        mk.typeval(Box::new(move |tyc| {
            let hir = tyc.ctx.lazy_hir(id)?;
            let inner = tyc
                .ctx
                .intern_ty(Ty::Named(hir.type_mark.span.into(), hir.type_mark.value));
            match hir.constraint {
                None => Ok(inner),
                Some(Spanned {
                    value: hir::Constraint::Range(ref con),
                    span,
                }) => tyc.apply_range_constraint(inner, Spanned::new(con, span)),
                Some(Spanned {
                    value: hir::Constraint::Array(ref ac),
                    span,
                }) => tyc.apply_array_constraint(inner, Spanned::new(ac, span)),
                Some(Spanned {
                    value: hir::Constraint::Record(ref rc),
                    span,
                }) => tyc.apply_record_constraint(inner, Spanned::new(rc, span)),
            }
        }));
    }
}
