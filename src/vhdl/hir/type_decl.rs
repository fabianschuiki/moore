// Copyright (c) 2018 Fabian Schuiki

//! Type and subtype declarations

use hir::prelude::*;

#[derive(Debug)]
pub struct TypeDecl2 {
    id: NodeId,
    span: Span,
    name: Spanned<Name>,
}

impl TypeDecl2 {
    pub fn walk<'a>(&'a self, visitor: &mut Visitor<'a>) {
        visitor.visit_name(self.name);
    }
}

impl<'t> FromAst<'t> for TypeDecl2 {
    type AllocInput = &'t ast::TypeDecl;
    type LatentInput = Self::AllocInput;
    type Context = AllocContext<'t>;
    type Latent = &'t Slot<'t, Self>;

    fn alloc_slot(ast: Self::AllocInput, context: Self::Context) -> Result<Self::Latent> {
        let slot = context.alloc(Slot::new(ast, context));
        context.define(ast.name.map(Into::into), Def2::Type(slot))?;
        Ok(slot)
    }

    fn from_ast(ast: Self::LatentInput, _context: Self::Context) -> Result<Self> {
        debugln!("create type decl {}", ast.name.value);
        Ok(TypeDecl2 {
            id: NodeId::alloc(),
            span: ast.span,
            name: ast.name,
        })
    }
}

impl<'t> Node<'t> for TypeDecl2 {
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

impl<'t> Decl2<'t> for TypeDecl2 {
    fn name(&self) -> Spanned<ResolvableName> {
        self.name.map(Into::into)
    }
}
