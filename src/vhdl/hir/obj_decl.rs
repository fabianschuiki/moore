// Copyright (c) 2018 Fabian Schuiki

//! Object declarations

use hir::prelude::*;

/// A constant declaration.
///
/// See IEEE 1076-2008 section 6.4.2.2.
#[derive(Debug)]
pub struct ConstDecl<'t> {
    span: Span,
    name: Spanned<Name>,
    ty: &'t (),
    init: Option<&'t ()>,
}

impl<'t> FromAst<'t> for ConstDecl<'t> {
    type AllocInput = &'t ast::ObjDecl;
    type LatentInput = (Span, Spanned<Name>, &'t (), Option<&'t ()>);
    type Context = AllocContext<'t>;
    type Latent = Vec<&'t Slot<'t, Self>>;

    fn alloc_slot(ast: Self::AllocInput, context: Self::Context) -> Result<Self::Latent> {
        let ty = &();
        let init = None;
        ast.names
            .iter()
            .map(|&name| {
                let name: Spanned<Name> = name.into();
                let slot: &_ = context.alloc(Slot::new((ast.span, name, ty, init), context));
                context.define(name.map_into(), Def2::Node(slot))?;
                Ok(slot)
            })
            .collect::<Vec<Result<_>>>()
            .into_iter()
            .collect()
    }

    fn from_ast((span, name, ty, init): Self::LatentInput, _context: Self::Context) -> Result<Self> {
        Ok(ConstDecl {
            span: span,
            name: name,
            ty: ty,
            init: init,
        })
    }
}

impl<'t> Node<'t> for ConstDecl<'t> {
    fn span(&self) -> Span {
        self.span
    }

    fn desc_kind(&self) -> String {
        "constant declaration".into()
    }

    fn desc_name(&self) -> String {
        format!("constant `{}`", self.name.value)
    }

    fn accept(&'t self, _visitor: &mut Visitor<'t>) {
        unimplemented!();
    }

    fn walk(&'t self, _visitor: &mut Visitor<'t>) {
        unimplemented!();
    }
}

impl<'t> Decl2<'t> for ConstDecl<'t> {
    fn name(&self) -> Spanned<ResolvableName> {
        self.name.map_into()
    }
}
