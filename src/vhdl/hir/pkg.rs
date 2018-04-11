// Copyright (c) 2018 Fabian Schuiki

//! Packages

#![allow(dead_code)]

use std::cell::RefCell;

use common::NodeId;
use common::name::Name;
use common::source::{Span, Spanned};

use arenas::Alloc;
use syntax::ast;

/// A placeholder for an HIR node.
pub struct Slot<'t, T: FromAst<'t> + 't>(RefCell<SlotState<'t, T>>);

#[derive(Copy, Clone)]
enum SlotState<'t, T: FromAst<'t> + 't> {
    Fresh(&'t AnyScope, T::Input),
    ReadyOk(&'t T),
    ReadyErr,
}

impl<'t, T: FromAst<'t>> Slot<'t, T> {
    /// Create a new slot.
    pub fn new(scope: &'t AnyScope, ast: T::Input) -> Slot<'t, T> {
        Slot(RefCell::new(SlotState::Fresh(scope, ast)))
    }

    /// Poll the slot, creating the HIR node from AST the first time.
    pub fn poll<A>(&self, arena: &'t A) -> Result<&'t T, ()>
    where
        A: Alloc<T>,
    {
        match *self.0.borrow() {
            SlotState::ReadyOk(x) => return Ok(x),
            SlotState::ReadyErr => return Err(()),
            _ => (),
        }
        ;
        let (scope, ast) = match self.0.replace(SlotState::ReadyErr) {
            SlotState::Fresh(scope, ast) => (scope, ast),
            _ => unreachable!(),
        };
        let node = T::from_ast(scope, ast).map(|x| arena.alloc(x) as &T);
        self.0.replace(match node {
            Ok(x) => SlotState::ReadyOk(x),
            Err(()) => SlotState::ReadyErr,
        });
        node
    }
}

impl<'t, T: FromAst<'t> + Node> Node for Slot<'t, T> {}

pub struct Package2<'t> {
    id: NodeId,
    span: Span,
    name: Spanned<Name>,
    scope: &'t AnyScope,
    decls: Vec<Box<Node + 't>>,
}

impl<'t> Package2<'t> {}

impl<'t> FromAst<'t> for Package2<'t> {
    type Input = &'t ast::PkgDecl;

    fn alloc_slot(scope: &'t AnyScope, ast: Self::Input) -> Result<Slot<'t, Self>, ()> {
        // TODO: register the package name in the scope
        Ok(Slot::new(scope, ast))
    }

    fn from_ast(scope: &'t AnyScope, ast: Self::Input) -> Result<Self, ()> {
        // TODO: create a new scope for the package
        let decls = ast.decls
            .iter()
            .flat_map(|decl| -> Option<Box<Node>> {
                match *decl {
                    ast::DeclItem::PkgDecl(ref decl) => Some(Box::new(Package2::alloc_slot(scope, decl).ok()?)),
                    ast::DeclItem::TypeDecl(ref decl) => Some(Box::new(TypeDecl2::alloc_slot(scope, decl).ok()?)),
                    _ => None,
                }
            })
            .collect::<Vec<_>>();
        Ok(Package2 {
            id: NodeId::alloc(),
            span: ast.span,
            name: ast.name,
            scope: scope,
            decls: decls,
        })
    }
}

impl<'t> Node for Package2<'t> {}

pub struct TypeDecl2 {
    id: NodeId,
    span: Span,
    name: Spanned<Name>,
}

impl<'t> FromAst<'t> for TypeDecl2 {
    type Input = &'t ast::TypeDecl;

    fn alloc_slot(scope: &'t AnyScope, ast: Self::Input) -> Result<Slot<'t, Self>, ()> {
        // TODO: register the type name in the scope
        Ok(Slot::new(scope, ast))
    }

    fn from_ast(_scope: &'t AnyScope, ast: Self::Input) -> Result<Self, ()> {
        Ok(TypeDecl2 {
            id: NodeId::alloc(),
            span: ast.span,
            name: ast.name,
        })
    }
}

impl Node for TypeDecl2 {}

pub trait AnyScope {}
pub trait Node {}

/// Construct something from an AST node.
pub trait FromAst<'t>: Sized {
    type Input;
    fn alloc_slot(scope: &'t AnyScope, ast: Self::Input) -> Result<Slot<'t, Self>, ()>;
    fn from_ast(scope: &'t AnyScope, ast: Self::Input) -> Result<Self, ()>;
}
