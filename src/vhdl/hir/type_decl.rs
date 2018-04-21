// Copyright (c) 2018 Fabian Schuiki

//! Type and subtype declarations

#![allow(unused_variables)]
#![allow(unused_imports)]

use hir::prelude::*;
use hir::{EnumLit, ExprContext, Range2};
use term::{self, TermContext};
use ty2::{AnyType, IntegerBasetype, IntegerRange, UniversalIntegerType};

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
    // /// An enumeration type.
    // Enum(Vec<EnumLit>),
    /// An integer or floating point type.
    Range(Spanned<Range2<'t>>),
    // /// A physical type.
    // Physical(Spanned<Range2<'t>>, PhysicalUnits),
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
            TypeData::Range(ref range) => {
                let (dir, lb, rb) = range.value.constant_value(ctx)?;
                assert_eq!(lb.ty(), rb.ty());
                let ty = lb.ty();
                match ty.as_any() {
                    AnyType::Integer(ty) => {
                        let lb = lb.as_any().unwrap_integer();
                        let rb = rb.as_any().unwrap_integer();
                        let ty = IntegerBasetype::new(IntegerRange::with_left_right(
                            dir,
                            lb.value().clone(),
                            rb.value().clone(),
                        ));
                        Ok(ctx.alloc(ty))
                    }
                    AnyType::Floating(ty) => unimplemented!(),
                    _ => {
                        ctx.emit(
                            DiagBuilder2::error("bounds must be of integer or floating-point type")
                                .span(range.span)
                                .add_note(format!("bounds are of type {}", ty)),
                        );
                        Err(())
                    }
                }
                // Err(())
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

fn unpack_type_data<'t>(
    data: &ast::TypeData,
    type_name: Spanned<Name>,
    context: AllocContext<'t>,
) -> Result<TypeData<'t>> {
    match *data {
        ast::RangeType(ref range_expr, ref units) => {
            let termctx = TermContext::new2(context);
            let range_expr = termctx.termify_expr(range_expr)?;
            let range = term::term_to_range(range_expr, context)?;
            if units.is_some() {
                panic!("units not yet implemented");
            }
            Ok(TypeData::Range(range))
        }
        _ => unimplemented!(
            "type `{}` unsupported type data {:#?}",
            type_name.value,
            data
        ),
    }
}
