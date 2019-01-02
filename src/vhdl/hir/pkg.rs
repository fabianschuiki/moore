// Copyright (c) 2018 Fabian Schuiki

//! Packages

use crate::hir::prelude::*;
use crate::hir::apply_use_clauses;
use crate::hir::TypeDecl2;

#[derive(Debug)]
pub struct Package2<'t> {
    id: NodeId,
    span: Span,
    name: Spanned<Name>,
    decls: Vec<&'t LatentNode<'t, Decl2<'t>>>,
    scope: &'t ScopeData<'t>,
}

impl<'t> Package2<'t> {
    /// Return the name of this package.
    pub fn name(&self) -> Spanned<Name> {
        self.name
    }

    /// Return the declarations made in this package.
    pub fn decls(&self) -> &[&'t LatentNode<'t, Decl2<'t>>] {
        &self.decls
    }

    /// Return the scope of the package.
    pub fn scope(&self) -> &'t ScopeData<'t> {
        self.scope
    }
}

impl<'t> FromAst<'t> for Package2<'t> {
    type AllocInput = &'t ast::PkgDecl;
    type LatentInput = Self::AllocInput;
    type Context = AllocContext<'t>;
    type Latent = &'t Slot<'t, Self>;

    fn alloc_slot(ast: Self::AllocInput, context: Self::Context) -> Result<Self::Latent> {
        let slot = context.alloc(Slot::new(ast, context));
        context.define(ast.name.map(Into::into), Def2::Pkg(slot))?;
        Ok(slot)
    }

    fn from_ast(ast: Self::LatentInput, context: Self::Context) -> Result<Self> {
        debugln!("create package decl {}", ast.name.value);
        let context = context.create_subscope();
        let mut uses = Vec::new();
        let decls = ast.decls
            .iter()
            .flat_map(|decl| -> Option<&'t LatentNode<'t, Decl2>> {
                match *decl {
                    ast::DeclItem::PkgDecl(ref decl) => Some(Package2::alloc_slot(decl, context).ok()?),
                    ast::DeclItem::TypeDecl(ref decl) => Some(TypeDecl2::alloc_slot(decl, context).ok()?),
                    ast::DeclItem::UseClause(_, ref clause) => {
                        uses.extend(clause.value.iter());
                        None
                    }
                    _ => None,
                }
            })
            .collect::<Vec<_>>();
        apply_use_clauses(uses.into_iter(), context);
        Ok(Package2 {
            id: NodeId::alloc(),
            span: ast.span,
            name: ast.name,
            decls: decls,
            scope: context.scope(),
        })
    }
}

impl<'t> Node<'t> for Package2<'t> {
    fn span(&self) -> Span {
        self.span
    }

    fn desc_kind(&self) -> String {
        "package".into()
    }

    fn desc_name(&self) -> String {
        format!("package `{}`", self.name.value)
    }

    fn accept(&'t self, visitor: &mut Visitor<'t>) {
        visitor.visit_pkg(self);
    }

    fn walk(&'t self, visitor: &mut Visitor<'t>) {
        visitor.visit_name(self.name);
        for decl in &self.decls {
            decl.accept(visitor);
        }
    }
}

impl<'t> Decl2<'t> for Package2<'t> {
    fn name(&self) -> Spanned<ResolvableName> {
        self.name.map(Into::into)
    }
}
