// Copyright (c) 2018 Fabian Schuiki

#![deny(missing_docs)]

use num::{BigInt, BigRational, ToPrimitive};

use crate::common::SessionContext;
use crate::common::errors::*;

use crate::hir::prelude::*;
use crate::ty2::{UniversalIntegerType, UniversalRealType};
use crate::konst2::{Const2, FloatingConst, IntegerConst};
pub use crate::syntax::ast::Dir;

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
    + AllocOwnedInto<'t, Type> {
}

impl<'t, T> ExprContext<'t> for T
where
    T: SessionContext
        + AllocInto<'t, IntegerConst<'t>>
        + AllocOwnedInto<'t, Const2<'t>>
        + AllocOwnedInto<'t, Type>,
{
}

/// A literal expression.
#[derive(Debug)]
pub struct LitExpr {
    span: Span,
    value: LitExprValue,
}

/// The value of a literal expression.
#[derive(Debug)]
pub enum LitExprValue {
    /// The value of an integer literal.
    Integer(BigInt),
    /// The value of a floating-point literal.
    Float(BigRational),
}

impl LitExpr {
    /// Create a new integer literal expression.
    pub fn new_integer(span: Span, value: BigInt) -> LitExpr {
        LitExpr {
            span: span,
            value: LitExprValue::Integer(value),
        }
    }

    /// Create a new float literal expression.
    pub fn new_float(span: Span, value: BigRational) -> LitExpr {
        LitExpr {
            span: span,
            value: LitExprValue::Float(value),
        }
    }

    /// Return the constant value of the literal.
    pub fn value(&self) -> &LitExprValue {
        &self.value
    }

    /// Check if this is an integer literal.
    pub fn is_integer(&self) -> bool {
        match self.value {
            LitExprValue::Integer(..) => true,
            _ => false,
        }
    }

    /// Check if this is a floating-point literal.
    pub fn is_float(&self) -> bool {
        match self.value {
            LitExprValue::Float(..) => true,
            _ => false,
        }
    }

    /// Return the literal's integer value, or `None` if it is not an integer.
    pub fn integer_value(&self) -> Option<&BigInt> {
        match self.value {
            LitExprValue::Integer(ref v) => Some(v),
            _ => None,
        }
    }

    /// Return the literal's float value, or `None` if it is not an float.
    pub fn float_value(&self) -> Option<&BigRational> {
        match self.value {
            LitExprValue::Float(ref v) => Some(v),
            _ => None,
        }
    }
}

impl<'t> Node<'t> for LitExpr {
    fn span(&self) -> Span {
        self.span
    }

    fn desc_kind(&self) -> String {
        match self.value {
            LitExprValue::Integer(..) => "integer literal".into(),
            LitExprValue::Float(..) => "floating-point literal".into(),
        }
    }

    fn accept(&'t self, visitor: &mut Visitor<'t>) {
        visitor.visit_literal_expr(self);
    }

    fn walk(&'t self, _visitor: &mut Visitor<'t>) {}
}

impl<'t> Expr2<'t> for LitExpr {
    fn typeval(&self, _: Option<&'t Type>, _: &ExprContext<'t>) -> Result<&'t Type> {
        Ok(match self.value {
            LitExprValue::Integer(..) => &UniversalIntegerType,
            LitExprValue::Float(..) => &UniversalRealType,
        })
    }

    fn constant_value(&self, ctx: &ExprContext<'t>) -> Result<&'t Const2<'t>> {
        Ok(ctx.alloc_owned(match self.value {
            LitExprValue::Integer(ref v) => IntegerConst::try_new(&UniversalIntegerType, v.clone())
                .emit(ctx)?
                .into_owned(),
            LitExprValue::Float(ref v) => {
                // Convert from BigRational to f64. This is ugly and stupid, but
                // good enough for the beginning.
                let f = v.numer().to_f64().unwrap() / v.denom().to_f64().unwrap();
                FloatingConst::try_new(&UniversalRealType, f)
                    .emit(ctx)?
                    .into_owned()
            }
        }))
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
