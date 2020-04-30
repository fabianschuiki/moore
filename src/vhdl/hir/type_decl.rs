// Copyright (c) 2016-2020 Fabian Schuiki

//! Type declarations

#![allow(unused_variables)]
#![allow(unused_imports)]

use num::BigInt;

use crate::hir::prelude::*;
use crate::hir::{EnumLit, ExprContext, Range2, SubtypeInd2};
use crate::term::{self, Term, TermContext};
use crate::ty2::*;

/// A type declaration.
///
/// See IEEE 1076-2008 section 6.2.
#[derive(Debug)]
pub struct TypeDecl2<'t> {
    span: Span,
    name: Spanned<Name>,
    data: Spanned<TypeData<'t>>,
}

/// The meat of a type declaration.
#[derive(Debug)]
enum TypeData<'t> {
    /// An incomplete type declaration.
    Incomplete,
    /// An enumeration type.
    Enum(Spanned<Vec<EnumLit>>),
    /// An integer or floating point type.
    Range(Spanned<Range2<'t>>),
    /// A physical type.
    Physical(Spanned<Range2<'t>>, Vec<PhysicalUnit>, usize),
    /// An access type.
    Access(&'t SubtypeInd2<'t>),
}

impl<'t> TypeDecl2<'t> {
    /// Return the declared type.
    ///
    /// This function maps the type declaration data to an actual `Type`.
    pub fn declared_type<C>(&self, ctx: C) -> Result<&'t Type>
    where
        C: ExprContext<'t> + Copy,
    {
        match self.data.value {
            TypeData::Incomplete => {
                ctx.emit(
                    DiagBuilder2::error(format!("type `{}` is incomplete", self.name.value))
                        .span(self.span)
                        .add_note(format!(
                            "Provide a declaration of the form `type {} is ...` somewhere.",
                            self.name.value
                        )),
                );
                Err(())
            }
            TypeData::Enum(ref literals) => {
                let ty = EnumBasetype::new(literals.value.iter().map(|x| match *x {
                    EnumLit::Ident(x) => EnumVariant::Ident(x.value),
                    EnumLit::Char(x) => EnumVariant::Char(x.value),
                }));
                Ok(ctx.alloc_owned(ty.into_owned()))
            }
            TypeData::Range(ref range) => {
                let (dir, lb, rb) = range.value.constant_value(ctx)?;
                assert_eq!(lb.ty(), rb.ty());
                let ty = lb.ty();
                match ty.as_any() {
                    AnyType::Integer(ty) => {
                        let lb = lb.as_any().unwrap_integer();
                        let rb = rb.as_any().unwrap_integer();
                        let ty = IntegerBasetype::new(Range::with_left_right(
                            dir,
                            lb.value().clone(),
                            rb.value().clone(),
                        ));
                        Ok(ctx.alloc_owned(ty.into_owned()))
                    }
                    AnyType::Floating(ty) => {
                        let lb = lb.as_any().unwrap_floating();
                        let rb = rb.as_any().unwrap_floating();
                        let ty = FloatingBasetype::new(Range::with_left_right(
                            dir,
                            lb.value().clone(),
                            rb.value().clone(),
                        ));
                        Ok(ctx.alloc_owned(ty.into_owned()))
                    }
                    _ => {
                        ctx.emit(
                            DiagBuilder2::error(format!(
                                "bounds of type `{}` must be of integer or floating-point type",
                                self.name.value
                            ))
                            .span(range.span)
                            .add_note(format!("bounds are of type {}", ty)),
                        );
                        Err(())
                    }
                }
            }
            TypeData::Physical(ref range, ref units, primary) => {
                let (dir, lb, rb) = range.value.constant_value(ctx)?;
                assert_eq!(lb.ty(), rb.ty());
                let ty = lb.ty();
                match ty.as_any() {
                    AnyType::Integer(ty) => {
                        let lb = lb.as_any().unwrap_integer();
                        let rb = rb.as_any().unwrap_integer();
                        let ty = PhysicalBasetype::new(
                            Range::with_left_right(dir, lb.value().clone(), rb.value().clone()),
                            units.clone(),
                            primary,
                        );
                        Ok(ctx.alloc_owned(ty.into_owned()))
                    }
                    _ => {
                        ctx.emit(
                            DiagBuilder2::error(format!(
                                "bounds of physical type `{}` must be integers",
                                self.name.value
                            ))
                            .span(range.span)
                            .add_note(format!("bounds are of type {}", ty)),
                        );
                        Err(())
                    }
                }
            }
            TypeData::Access(subtype) => {
                let ty = AccessType::new(subtype.declared_type(ctx)?);
                Ok(ctx.alloc_owned(ty.into_owned()))
            }
        }
    }
}

impl<'t> FromAst<'t> for TypeDecl2<'t> {
    type AllocInput = &'t ast::TypeDecl;
    type LatentInput = Self::AllocInput;
    type Context = AllocContext<'t>;
    type Latent = &'t Slot<'t, Self>;

    fn alloc_slot(ast: Self::AllocInput, context: Self::Context) -> Result<Self::Latent> {
        let slot = context.alloc(Slot::new(ast, context));
        // TODO: Make the definition weak such that an actual type definition
        // may override it.
        context.define(ast.name.map_into(), Def2::Type(slot))?;
        if let Some(ref data) = ast.data {
            define_auxiliary_names(&data.value, slot, context)?;
        }
        Ok(slot)
    }

    fn from_ast(ast: Self::LatentInput, context: Self::Context) -> Result<Self> {
        let data = match ast.data {
            Some(ref data) => {
                Spanned::new(unpack_type_data(&data.value, ast.name, context)?, data.span)
            }
            None => Spanned::new(TypeData::Incomplete, ast.span),
        };
        Ok(TypeDecl2 {
            span: ast.span,
            name: ast.name,
            data: data,
        })
    }
}

impl<'t> Node<'t> for TypeDecl2<'t> {
    fn span(&self) -> Span {
        self.span
    }

    fn desc_kind(&self) -> String {
        "type declaration".into()
    }

    fn desc_name(&self) -> String {
        format!("type declaration `{}`", self.name.value)
    }

    fn accept(&'t self, visitor: &mut Visitor<'t>) {
        visitor.visit_type_decl(self);
    }

    fn walk(&'t self, visitor: &mut Visitor<'t>) {
        visitor.visit_name(self.name);
    }
}

impl<'t> Decl2<'t> for TypeDecl2<'t> {
    fn name(&self) -> Spanned<ResolvableName> {
        self.name.map_into()
    }
}

/// Define additional names in the scope, e.g. for enums and physical types.
fn define_auxiliary_names<'t>(
    data: &ast::TypeData,
    type_decl: &'t LatentNode<'t, TypeDecl2<'t>>,
    context: AllocContext<'t>,
) -> Result<()> {
    match *data {
        ast::EnumType(ref paren_elems) => {
            for (i, lit) in paren_elems.value.iter().enumerate() {
                match lit.expr.data {
                    ast::NameExpr(ref name) => context.define(
                        ResolvableName::from_primary_name(&name.primary, context)?,
                        Def2::Enum(TypeVariantDef(type_decl, i)),
                    )?,
                    _ => (),
                }
            }
        }
        ast::RangeType(_, Some(ref units)) => {
            for (i, unit) in units.iter().enumerate() {
                context.define(
                    Spanned::new(unit.0.name.into(), unit.0.span),
                    Def2::Unit(TypeVariantDef(type_decl, i)),
                )?;
            }
        }
        _ => (),
    }
    Ok(())
}

/// Map an AST type data to the corresponding HIR type data.
fn unpack_type_data<'t>(
    data: &'t ast::TypeData,
    type_name: Spanned<Name>,
    context: AllocContext<'t>,
) -> Result<TypeData<'t>> {
    match *data {
        ast::EnumType(ref paren_elems) => {
            let literals = paren_elems
                .value
                .iter()
                .map(|elem| match paren_elem_to_enum_literal(elem) {
                    Some(x) => Ok(x),
                    None => {
                        context.emit(
                            DiagBuilder2::error(format!(
                                "`{}` is not an enumeration literal",
                                elem.span.extract()
                            ))
                            .span(elem.span)
                            .add_note("expected an identifier or character literal"),
                        );
                        Err(())
                    }
                })
                .collect::<Vec<Result<_>>>()
                .into_iter()
                .collect::<Result<Vec<_>>>()?;
            Ok(TypeData::Enum(Spanned::new(literals, paren_elems.span)))
        }
        ast::RangeType(ref range_expr, ref units) => {
            let termctx = TermContext::new2(context);
            let range_expr = termctx.termify_expr(range_expr)?;
            let range = term::term_to_range(range_expr, context)?;
            match *units {
                Some(ref units) => {
                    let (units, primary) = unpack_units(units, type_name, context)?;
                    Ok(TypeData::Physical(range, units, primary))
                }
                None => Ok(TypeData::Range(range)),
            }
        }
        ast::AccessType(ref subty) => {
            let subty = context.alloc(SubtypeInd2::from_ast(subty, context)?);
            Ok(TypeData::Access(subty))
        }
        _ => unimplemented!(
            "type `{}` unsupported type data {:#?}",
            type_name.value,
            data
        ),
    }
}

/// Unpack the units of a physical type declaration.
fn unpack_units<'t>(
    units: &[(ast::Ident, Option<Box<ast::Expr>>)],
    type_name: Spanned<Name>,
    ctx: AllocContext<'t>,
) -> Result<(Vec<PhysicalUnit>, usize)> {
    // Determine the primary unit.
    let mut prim_iter = units
        .iter()
        .enumerate()
        .filter(|&(_, &(_, ref expr))| expr.is_none())
        .map(|(index, &(name, _))| (index, name));
    let primary = match prim_iter.next() {
        Some(u) => u,
        None => {
            ctx.emit(
                DiagBuilder2::error(format!(
                    "physical type `{}` has no primary unit",
                    type_name.value
                ))
                .span(type_name.span)
                .add_note(
                    "A physical type must have a primary unit of the form `<name>;`. \
                         See IEEE 1076-2008 section 5.2.4.",
                ),
            );
            return Err(());
        }
    };
    let mut had_fails = false;
    for (_, n) in prim_iter {
        ctx.emit(
            DiagBuilder2::error(format!(
                "physical type `{}` has multiple primary units",
                type_name.value
            ))
            .span(n.span)
            .add_note(
                "A physical type cannot have multiple primary units. \
                     See IEEE 1076-2008 section 5.2.4.",
            ),
        );
        had_fails = true;
    }
    if had_fails {
        return Err(());
    }

    // Determine the units and how they are defined with respect
    // to each other.
    let term_ctx = TermContext::new2(ctx);
    let table = units
        .iter()
        .map(|&(unit_name, ref expr)| {
            let rel = if let Some(ref expr) = *expr {
                let term = term_ctx.termify_expr(expr)?;
                let (value, unit) = match term.value {
                    Term::PhysLit(value, unit) => (value, unit),
                    _ => {
                        ctx.emit(
                            DiagBuilder2::error(format!(
                                "`{}` is not a valid secondary unit",
                                term.span.extract()
                            ))
                            .span(term.span),
                        );
                        debugln!("It is a {:#?}", term.value);
                        return Err(());
                    }
                };
                // TODO: Find a way to enable this again!
                // if unit.value.0 != id {
                //     ctx.emit(
                //         DiagBuilder2::error(format!(
                //             "`{}` is not a unit in the physical type `{}`",
                //             term.span.extract(),
                //             type_name.value
                //         )).span(term.span)
                //             .add_note(format!("`{}` has been declared here:", term.span.extract()
                // ))
                //             .span(unit.span),
                //     );
                // }
                Some((value, unit.value.unwrap_new().1))
            } else {
                None
            };
            Ok((Spanned::new(unit_name.name, unit_name.span), rel))
        })
        .collect::<Vec<Result<_>>>()
        .into_iter()
        .collect::<Result<Vec<_>>>()?;

    // Determine the scale of each unit with respect to the primary unit.
    Ok((
        table
            .iter()
            .map(|&(name, ref rel)| {
                let mut abs = BigInt::from(1);
                let mut rel_to = rel.as_ref();
                while let Some(&(ref scale, index)) = rel_to {
                    abs = abs * scale;
                    rel_to = table[index].1.as_ref();
                }
                PhysicalUnit::new(name.value, abs, rel.clone())
            })
            .collect::<Vec<_>>(),
        primary.0,
    ))
}

/// Unpack a parenthesis element as an enumeration literal.
fn paren_elem_to_enum_literal(elem: &ast::ParenElem) -> Option<EnumLit> {
    if !elem.choices.value.is_empty() {
        None
    } else {
        match elem.expr.data {
            ast::NameExpr(ast::CompoundName {
                primary: ast::PrimaryName { kind, span, .. },
                ref parts,
                ..
            }) if parts.is_empty() => match kind {
                ast::PrimaryNameKind::Ident(n) => Some(EnumLit::Ident(Spanned::new(n, span))),
                ast::PrimaryNameKind::Char(c) => Some(EnumLit::Char(Spanned::new(c, span))),
                _ => None,
            },
            _ => None,
        }
    }
}
