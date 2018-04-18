// Copyright (c) 2018 Fabian Schuiki

use hir::prelude::*;
pub use syntax::ast::Dir;

/// An expression.
///
/// See the actual concrete expression
///
/// See IEEE 1076-2008 section 9.
pub trait Expr2<'t>: Node<'t> {}

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
