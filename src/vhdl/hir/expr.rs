// Copyright (c) 2018 Fabian Schuiki

use num::BigInt;

use hir::prelude::*;
pub use syntax::ast::Dir;
use ty2::UniversalIntegerType;

/// An expression.
///
/// See IEEE 1076-2008 section 9.
pub trait Expr2<'t>: Node<'t> {
    fn typeval(
        &self,
        tyctx: Option<&'t Type>,
        ctx: &AllocInto<'t, UniversalIntegerType>,
    ) -> Result<&'t Type>;
}

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
    fn typeval(
        &self,
        _: Option<&'t Type>,
        ctx: &AllocInto<'t, UniversalIntegerType>,
    ) -> Result<&'t Type> {
        Ok(ctx.alloc(UniversalIntegerType))
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
    Immediate(Span, Spanned<Dir>, &'t Expr2<'t>, &'t Expr2<'t>),
}

impl<'t> Range2<'t> {
    /// Determine the type of the range.
    ///
    /// This determines the type of the range's bounds and applies any necessary
    /// implicit casts to make them be of the same type.
    pub fn bound_type<C>(&self, ctx: C) -> Result<&'t Type>
    where
        C: AllocInto<'t, UniversalIntegerType> + DiagEmitter,
    {
        match *self {
            Range2::Immediate(span, _, l, r) => {
                let lt = l.typeval(None, &ctx);
                let rt = r.typeval(None, &ctx);
                let (lt, rt) = (lt?, rt?);
                debugln!("lt = {}", lt);
                debugln!("rt = {}", rt);
                if lt == rt {
                    Ok(lt)
                } else if lt.is_implicitly_castable(rt) {
                    Ok(rt)
                } else if rt.is_implicitly_castable(lt) {
                    Ok(lt)
                } else {
                    ctx.emit(
                        DiagBuilder2::error(format!(
                            "types of range bounds `{}` and `{}` are incompatible",
                            l.span().extract(),
                            r.span().extract()
                        )).span(span)
                            .add_note(format!("left bound type: {}", lt))
                            .add_note(format!("right bound type: {}", rt)),
                    );
                    Err(())
                }
            }
        }
    }

    /// Determine the constant value of the range.
    pub fn constant_value<C>(&self, ctx: C) -> Result<(Dir, (), ())>
    where
        C: AllocInto<'t, UniversalIntegerType> + DiagEmitter,
    {
        let ty = self.bound_type(ctx)?;
        debugln!("bound type is {}", ty);
        match *self {
            Range2::Immediate(_, d, l, r) => {
                debugln!("const value of range {:?} {} {:?}", l, d.value, r);
                Ok((d.value, (), ()))
            }
        }
    }
}
