// Copyright (c) 2018 Fabian Schuiki

//! Visitor pattern for the HIR.

use crate::hir::*;

/// Provides HIR traversal.
pub trait Visitor<'t> {
    /// Get a `&mut Visitor` reference to `self`.
    fn as_visitor(&mut self) -> &mut Visitor<'t>;

    fn visit_name(&mut self, _: Spanned<Name>) {}

    fn visit_library(&mut self, hir: &'t Library<'t>) {
        hir.walk(self.as_visitor());
    }

    fn visit_pkg(&mut self, hir: &'t Package2<'t>) {
        hir.walk(self.as_visitor());
    }

    fn visit_type_decl(&mut self, hir: &'t TypeDecl2<'t>) {
        hir.walk(self.as_visitor());
    }

    fn visit_subtype_ind(&mut self, hir: &'t SubtypeInd2<'t>) {
        hir.walk(self.as_visitor());
    }

    fn visit_literal_expr(&mut self, _: &'t LitExpr) {}
}
