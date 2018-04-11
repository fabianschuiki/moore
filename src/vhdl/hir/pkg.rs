// Copyright (c) 2018 Fabian Schuiki

//! Packages

#![allow(dead_code)]

use std::cell::RefCell;

use common::NodeId;
use common::name::Name;
use common::source::{Span, Spanned, INVALID_SPAN};

use arenas::{Alloc, AllocInto};
use syntax::ast;

/// A placeholder for an HIR node.
pub struct Slot<'t, T>(RefCell<SlotState<'t, T>>)
where
    T: FromAst<'t> + 't;

#[derive(Copy, Clone)]
enum SlotState<'t, T>
where
    T: FromAst<'t> + 't,
{
    Fresh(&'t AnyScope, T::Input, T::Arena),
    ReadyOk(&'t T),
    ReadyErr,
}

impl<'t, T> Slot<'t, T>
where
    T: FromAst<'t>,
    T::Arena: AllocInto<'t, T> + Clone,
{
    /// Create a new slot.
    pub fn new(scope: &'t AnyScope, ast: T::Input, arena: T::Arena) -> Slot<'t, T> {
        Slot(RefCell::new(SlotState::Fresh(scope, ast, arena)))
    }

    /// Poll the slot, creating the HIR node from the AST the first time.
    pub fn poll(&self) -> Result<&'t T, ()> {
        match *self.0.borrow() {
            SlotState::ReadyOk(x) => return Ok(x),
            SlotState::ReadyErr => return Err(()),
            _ => (),
        }
        let (scope, ast, arena) = match self.0.replace(SlotState::ReadyErr) {
            SlotState::Fresh(scope, ast, arena) => (scope, ast, arena),
            _ => unreachable!(),
        };
        let node = T::from_ast(scope, ast, arena.clone()).map(|x| arena.alloc(x) as &T);
        self.0.replace(match node {
            Ok(x) => SlotState::ReadyOk(x),
            Err(()) => SlotState::ReadyErr,
        });
        node
    }
}

impl<'t, T> Node for Slot<'t, T>
where
    T: FromAst<'t> + Node,
    T::Arena: AllocInto<'t, T> + Clone,
{
    fn span(&self) -> Span {
        self.poll().map(Node::span).unwrap_or(INVALID_SPAN)
    }
}

pub struct Package2<'t> {
    id: NodeId,
    span: Span,
    name: Spanned<Name>,
    scope: &'t AnyScope,
    decls: Vec<Box<Node + 't>>,
}

impl<'t> FromAst<'t> for Package2<'t> {
    type Input = &'t ast::PkgDecl;
    type Arena = &'t Alloc<Self>;

    fn alloc_slot(
        scope: &'t AnyScope,
        ast: Self::Input,
        arena: Self::Arena,
    ) -> Result<Slot<'t, Self>, ()> {
        // TODO: register the package name in the scope
        Ok(Slot::new(scope, ast, arena))
    }

    fn from_ast(scope: &'t AnyScope, ast: Self::Input, _arena: Self::Arena) -> Result<Self, ()> {
        // TODO: create a new scope for the package
        let decls = ast.decls
            .iter()
            .flat_map(|decl| -> Option<Box<Node>> {
                match *decl {
                    // ast::DeclItem::PkgDecl(ref decl) => {
                    //     Some(Box::new(Package2::alloc_slot(scope, decl, arena).ok()?))
                    // }
                    // ast::DeclItem::TypeDecl(ref decl) => {
                    //     Some(Box::new(TypeDecl2::alloc_slot(scope, decl, arena).ok()?))
                    // }
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

impl<'t> Node for Package2<'t> {
    fn span(&self) -> Span {
        self.span
    }
}

pub struct TypeDecl2 {
    id: NodeId,
    span: Span,
    name: Spanned<Name>,
}

impl<'t> FromAst<'t> for TypeDecl2 {
    type Input = &'t ast::TypeDecl;
    type Arena = &'t Alloc<Self>;

    fn alloc_slot(
        scope: &'t AnyScope,
        ast: Self::Input,
        arena: Self::Arena,
    ) -> Result<Slot<'t, Self>, ()> {
        // TODO: register the type name in the scope
        Ok(Slot::new(scope, ast, arena))
    }

    fn from_ast(_scope: &'t AnyScope, ast: Self::Input, _arena: Self::Arena) -> Result<Self, ()> {
        Ok(TypeDecl2 {
            id: NodeId::alloc(),
            span: ast.span,
            name: ast.name,
        })
    }
}

impl Node for TypeDecl2 {
    fn span(&self) -> Span {
        self.span
    }
}

pub trait AnyScope {}

pub trait Node {
    /// The source file location of this node.
    fn span(&self) -> Span;
}

/// Construct something from an AST node.
pub trait FromAst<'t>: Sized {
    type Input;
    type Arena;

    fn alloc_slot(
        scope: &'t AnyScope,
        ast: Self::Input,
        arena: Self::Arena,
    ) -> Result<Slot<'t, Self>, ()>;

    fn from_ast(scope: &'t AnyScope, ast: Self::Input, arena: Self::Arena) -> Result<Self, ()>;
}
