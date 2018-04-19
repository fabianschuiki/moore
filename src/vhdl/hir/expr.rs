// Copyright (c) 2018 Fabian Schuiki

use num::BigInt;

use hir::prelude::*;
pub use syntax::ast::Dir;

/// An expression.
///
/// See IEEE 1076-2008 section 9.
pub trait Expr2<'t>: Node<'t> {}

#[derive(Debug)]
pub struct IntLitExpr {
    span: Span,
    value: BigInt,
}

impl IntLitExpr {
    /// Create a new integer literal expression.
    pub fn new(span: Span, value: BigInt) -> IntLitExpr {
        IntLitExpr {
            span: span,
            value: value,
        }
    }

    /// Return the constant value of the literal.
    pub fn value(&self) -> &BigInt {
        &self.value
    }
}

impl<'t> Node<'t> for IntLitExpr {
    fn span(&self) -> Span {
        self.span
    }

    fn desc_kind(&self) -> String {
        "integer literal".into()
    }

    fn accept(&'t self, visitor: &mut Visitor<'t>) {
        visitor.visit_integer_literal_expr(self);
    }

    fn walk(&'t self, visitor: &mut Visitor<'t>) {}
}

impl<'t> Expr2<'t> for IntLitExpr {}

/// A range.
///
/// See IEEE 1076-2008 section 5.2.1.
///
/// ```text
/// range := range.attribute_name | simple_expression direction simple_expression
/// ```
#[derive(Debug)]
pub enum Range2<'t> {
    // Attr(AttrRef),
    Immediate(Dir, &'t Expr2<'t>, &'t Expr2<'t>),
}
