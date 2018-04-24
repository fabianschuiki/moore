// Copyright (c) 2018 Fabian Schuiki

#![deny(missing_docs)]

use num::BigInt;

use common::SessionContext;
use common::errors::*;

use hir::prelude::*;
use ty2::{IntegerBasetype, UniversalIntegerType};
use konst2::{Const2, IntegerConst};
pub use syntax::ast::Dir;

/// An expression.
///
/// See IEEE 1076-2008 section 9.
pub trait Expr2<'t>: Node<'t> {
    /// Determine the type of the expression.
    fn typeval(&self, tyctx: Option<&'t Type>, ctx: &ExprContext<'t>) -> Result<&'t Type>;

    /// Determine the constant value of the expression.
    ///
    /// Emits diagnostic errors if the expression has no constant value.
    fn constant_value(&self, ctx: &ExprContext<'t>) -> Result<&'t Const2<'t>>;
}

/// A context that provides the facilities to operate on expressions.
pub trait ExprContext<'t>
    : SessionContext
    + AllocInto<'t, IntegerConst<'t>>
    + AllocOwnedInto<'t, Const2<'t>>
    + AllocInto<'t, IntegerBasetype> {
}

impl<'t, T> ExprContext<'t> for T
where
    T: SessionContext
        + AllocInto<'t, IntegerConst<'t>>
        + AllocOwnedInto<'t, Const2<'t>>
        + AllocInto<'t, IntegerBasetype>,
{
}

/// An integer literal expression.
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

    fn walk(&'t self, _visitor: &mut Visitor<'t>) {}
}

impl<'t> Expr2<'t> for IntLitExpr {
    fn typeval(&self, _: Option<&'t Type>, _: &ExprContext<'t>) -> Result<&'t Type> {
        Ok(&UniversalIntegerType)
    }

    fn constant_value(&self, ctx: &ExprContext<'t>) -> Result<&'t Const2<'t>> {
        Ok(ctx.alloc(IntegerConst::try_new(&UniversalIntegerType, self.value.clone()).emit(ctx)?))
    }
}

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
    /// An range given by two immediate values.
    Immediate(Span, Spanned<Dir>, &'t Expr2<'t>, &'t Expr2<'t>),
}

impl<'t> Range2<'t> {
    /// Determine the type of the range.
    ///
    /// This determines the type of the range's bounds and applies any necessary
    /// implicit casts to make them be of the same type.
    pub fn bound_type<C>(&self, ctx: C) -> Result<&'t Type>
    where
        C: ExprContext<'t> + Copy,
    {
        match *self {
            Range2::Immediate(span, _, l, r) => {
                let lt = l.typeval(None, &ctx);
                let rt = r.typeval(None, &ctx);
                let (lt, rt) = (lt?, rt?);
                if lt == rt {
                    Ok(lt)
                } else if lt.is_implicitly_castable(rt) {
                    Ok(rt)
                } else if rt.is_implicitly_castable(lt) {
                    Ok(lt)
                } else {
                    ctx.emit(
                        DiagBuilder2::error(format!(
                            "range bounds `{}` and `{}` have incompatible types",
                            l.span().extract(),
                            r.span().extract()
                        )).span(span)
                            .add_note(format!(" left bound type: {}", lt))
                            .add_note(format!("right bound type: {}", rt)),
                    );
                    Err(())
                }
            }
        }
    }

    /// Determine the constant value of the range.
    pub fn constant_value<C>(&self, ctx: C) -> Result<(Dir, &'t Const2<'t>, &'t Const2<'t>)>
    where
        C: ExprContext<'t> + Copy,
    {
        let ty = self.bound_type(ctx)?;
        match *self {
            Range2::Immediate(_, d, l, r) => {
                let lc = l.constant_value(&ctx).and_then(|x| x.cast(ty).emit(ctx));
                let rc = r.constant_value(&ctx).and_then(|x| x.cast(ty).emit(ctx));
                Ok((d.value, ctx.maybe_alloc(lc?), ctx.maybe_alloc(rc?)))
            }
        }
    }
}
