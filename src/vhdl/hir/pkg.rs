// Copyright (c) 2018 Fabian Schuiki

//! Packages

#![allow(dead_code)]

use common::NodeId;
use common::name::Name;
use common::source::{Span, Spanned};
use common::score::Result;

use hir::prelude::*;
use arenas::{Alloc, AllocInto};
use syntax::ast;
use score::ResolvableName;
use scope2::{Def2, ScopeContext, ScopeData};
use hir::visit::Visitor;
use hir::apply_use_clauses;
use hir::{Decl2, FromAst, LatentNode, Node, Slot};

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
    type Input = &'t ast::PkgDecl;
    type Context = AllocContext<'t>;

    fn alloc_slot(ast: Self::Input, context: Self::Context) -> Result<&'t Slot<'t, Self>> {
        let slot = context.alloc(Slot::new(ast, context));
        context.define(ast.name.map(Into::into), Def2::Pkg(slot))?;
        Ok(slot)
    }

    fn from_ast(ast: Self::Input, context: Self::Context) -> Result<Self> {
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
    type Input = &'t ast::TypeDecl;
    type Context = AllocContext<'t>;

    fn alloc_slot(ast: Self::Input, context: Self::Context) -> Result<&'t Slot<'t, Self>> {
        let slot = context.alloc(Slot::new(ast, context));
        context.define(ast.name.map(Into::into), Def2::Type(slot))?;
        Ok(slot)
    }

    fn from_ast(ast: Self::Input, _arena: Self::Context) -> Result<Self> {
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
