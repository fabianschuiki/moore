// Copyright (c) 2018 Fabian Schuiki

//! Subtype declarations

#![allow(unused_variables)]
#![allow(unused_imports)]

use num::BigInt;

use crate::hir::prelude::*;
use crate::hir::{EnumLit, ExprContext, Range2};
use crate::term::{self, Term, TermContext};
use crate::ty2::{AnyType, EnumBasetype, EnumVariant, FloatingBasetype, IntegerBasetype, IntegerRange,
          PhysicalBasetype, PhysicalUnit, Range, UniversalIntegerType};

/// A subtype declaration.
///
/// See IEEE 1076-2008 section 6.3.
#[derive(Debug)]
pub struct SubtypeDecl2<'t> {
    span: Span,
    name: Spanned<Name>,
    data: Spanned<&'t Slot<'t, SubtypeInd2<'t>>>,
}

/// A subtype indication.
///
/// See IEEE 1076-2008 section 6.3.
#[derive(Debug)]
pub struct SubtypeInd2<'t> {
    span: Span,
    marker: &'t (),
}

impl<'t> SubtypeInd2<'t> {
    /// Return the indicated type.
    ///
    /// This function maps the subtype indication data to an actual `Type`.
    pub fn declared_type<C>(&self, ctx: C) -> Result<&'t Type>
    where
        C: ExprContext<'t> + Copy,
    {
        unimplemented!("declared_type of a subtype indication")
    }
}

impl<'t> FromAst<'t> for SubtypeInd2<'t> {
    type AllocInput = &'t ast::SubtypeInd;
    type LatentInput = Self::AllocInput;
    type Context = AllocContext<'t>;
    type Latent = &'t Slot<'t, Self>;

    fn alloc_slot(ast: Self::AllocInput, context: Self::Context) -> Result<Self::Latent> {
        let slot = context.alloc(Slot::new(ast, context));
        Ok(slot)
    }

    fn from_ast(ast: Self::LatentInput, context: Self::Context) -> Result<Self> {
        Ok(SubtypeInd2 {
            span: ast.span,
            marker: &(),
        })
    }
}

impl<'t> Node<'t> for SubtypeInd2<'t> {
    fn span(&self) -> Span {
        self.span
    }

    fn desc_kind(&self) -> String {
        "subtype indication".into()
    }

    fn desc_name(&self) -> String {
        self.desc_kind()
    }

    fn accept(&'t self, visitor: &mut Visitor<'t>) {
        visitor.visit_subtype_ind(self);
    }

    fn walk(&'t self, visitor: &mut Visitor<'t>) {}
}
