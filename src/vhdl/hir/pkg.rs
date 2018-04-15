// Copyright (c) 2018 Fabian Schuiki

//! Packages

#![allow(dead_code)]

use std;
use std::cell::RefCell;

use common::NodeId;
use common::name::Name;
use common::source::{Span, Spanned, INVALID_SPAN};

use arenas::{Alloc, AllocInto};
use syntax::ast;
use score::ResolvableName;

pub type Result<T> = std::result::Result<T, ()>;

make_arenas!(
    pub struct Arenas2<'t> {
        package:   Package2<'t>,
        type_decl: TypeDecl2,
        package_slot: Slot<'t, Package2<'t>>,
        type_decl_slot: Slot<'t, TypeDecl2>,
    }
);

/// A placeholder for an HIR node.
pub struct Slot<'t, T>(RefCell<SlotState<'t, T>>)
where
    T: FromAst<'t> + 't;

#[derive(Copy, Clone)]
enum SlotState<'t, T>
where
    T: FromAst<'t> + 't,
{
    Fresh(T::Input, T::Context),
    ReadyOk(&'t T),
    ReadyErr,
}

impl<'t, T> Slot<'t, T>
where
    T: FromAst<'t>,
    T::Context: AllocInto<'t, T> + Clone,
{
    /// Create a new slot.
    pub fn new(ast: T::Input, context: T::Context) -> Slot<'t, T> {
        Slot(RefCell::new(SlotState::Fresh(ast, context)))
    }

    /// Poll the slot, creating the HIR node from the AST the first time.
    pub fn poll(&self) -> Result<&'t T> {
        match *self.0.borrow() {
            SlotState::ReadyOk(x) => return Ok(x),
            SlotState::ReadyErr => return Err(()),
            _ => (),
        }
        let (ast, context) = match self.0.replace(SlotState::ReadyErr) {
            SlotState::Fresh(ast, context) => (ast, context),
            _ => unreachable!(),
        };
        let node = T::from_ast(ast, context.clone()).map(|x| context.alloc(x) as &T);
        self.0.replace(match node {
            Ok(x) => SlotState::ReadyOk(x),
            Err(()) => SlotState::ReadyErr,
        });
        node
    }
}

impl<'t, T> LatentNode<'t> for Slot<'t, T>
where
    T: FromAst<'t> + Node,
    T::Context: AllocInto<'t, T> + Clone,
{
    fn poll(&self) -> Result<&'t Node> {
        Slot::poll(self).map(|n| n as &Node)
    }
}

pub struct Package2<'t> {
    id: NodeId,
    span: Span,
    name: Spanned<Name>,
    decls: Vec<&'t LatentNode<'t>>,
}

impl<'t> Package2<'t> {
    pub fn decls(&self) -> &[&'t LatentNode<'t>] {
        &self.decls
    }
}

impl<'t> FromAst<'t> for Package2<'t> {
    type Input = &'t ast::PkgDecl;
    type Context = Context<'t>;

    fn alloc_slot(ast: Self::Input, context: Self::Context) -> Result<&'t Slot<'t, Self>> {
        // TODO: register the package name in the scope
        let slot = context.alloc(Slot::new(ast, context));
        context.define(ast.name.map(Into::into), Def2::Pkg(slot))?;
        Ok(slot)
    }

    fn from_ast(ast: Self::Input, context: Self::Context) -> Result<Self> {
        debugln!("create package decl {}", ast.name.value);
        // TODO: create a new scope for the package
        let decls = ast.decls
            .iter()
            .flat_map(|decl| -> Option<&'t LatentNode> {
                match *decl {
                    ast::DeclItem::PkgDecl(ref decl) => {
                        Some(Package2::alloc_slot(decl, context).ok()?)
                    }
                    ast::DeclItem::TypeDecl(ref decl) => {
                        Some(TypeDecl2::alloc_slot(decl, context).ok()?)
                    }
                    _ => None,
                }
            })
            .collect::<Vec<_>>();
        Ok(Package2 {
            id: NodeId::alloc(),
            span: ast.span,
            name: ast.name,
            decls: decls,
        })
    }
}

impl<'t> Node for Package2<'t> {
    fn span(&self) -> Span {
        self.span
    }

    fn desc_kind(&self) -> String {
        "package".into()
    }

    fn desc_name(&self) -> String {
        format!("package `{}`", self.name.value)
    }
}

pub struct TypeDecl2 {
    id: NodeId,
    span: Span,
    name: Spanned<Name>,
}

impl<'t> FromAst<'t> for TypeDecl2 {
    type Input = &'t ast::TypeDecl;
    type Context = Context<'t>;

    fn alloc_slot(ast: Self::Input, context: Self::Context) -> Result<&'t Slot<'t, Self>> {
        // TODO: register the type name in the scope
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

impl Node for TypeDecl2 {
    fn span(&self) -> Span {
        self.span
    }

    fn desc_kind(&self) -> String {
        "type declaration".into()
    }

    fn desc_name(&self) -> String {
        format!("type declaration `{}`", self.name.value)
    }
}

pub trait AnyScope {}

pub trait Node {
    /// The source file location of this node.
    fn span(&self) -> Span;

    /// A human-readable description of the node's kind.
    ///
    /// For example "package" or "entity".
    fn desc_kind(&self) -> String;

    /// A human-readable description of the node, including its name.
    ///
    /// E.g. `package 'foo'` or `entity 'adder'`.
    fn desc_name(&self) -> String {
        self.desc_kind()
    }
}

/// Lazily resolve to a `Node`.
pub trait LatentNode<'t> {
    /// Access the underlying node.
    ///
    /// On the first time this function is called, the node is created.
    /// Subsequent calls are guaranteed to return the same node. Node creation
    /// may fail for a variety of reasons, thus the function returns a `Result`.
    fn poll(&self) -> Result<&'t Node>;
}

/// Construct something from an AST node.
pub trait FromAst<'t>: Sized {
    type Input: 't;
    type Context: 't;

    fn alloc_slot(ast: Self::Input, context: Self::Context) -> Result<&'t Slot<'t, Self>>;

    fn from_ast(ast: Self::Input, context: Self::Context) -> Result<Self>;
}

#[derive(Copy, Clone)]
pub struct Context<'t> {
    pub arenas: &'t Arenas2<'t>,
    pub scope: &'t Scope<'t>,
}

impl<'t> Context<'t> {
    pub fn new(arenas: &'t Arenas2<'t>, scope: &'t Scope<'t>) -> Context<'t> {
        Context {
            arenas: arenas,
            scope: scope,
        }
    }
}

impl<'t, T> AllocInto<'t, T> for Context<'t>
where
    Arenas2<'t>: Alloc<T>,
{
    fn alloc(&self, value: T) -> &'t mut T {
        self.arenas.alloc(value)
    }
}

impl<'t> Scope<'t> for Context<'t> {
    fn define(&self, name: Spanned<ResolvableName>, def: Def2<'t>) -> Result<()> {
        self.scope.define(name, def)
    }
}

pub trait Scope<'t> {
    fn define(&self, name: Spanned<ResolvableName>, def: Def2<'t>) -> Result<()>;
}

pub enum Def2<'t> {
    Pkg(&'t Slot<'t, Package2<'t>>),
    Type(&'t Slot<'t, TypeDecl2>),
}

pub struct DummyScope;

impl<'t> Scope<'t> for DummyScope {
    fn define(&self, name: Spanned<ResolvableName>, _def: Def2<'t>) -> Result<()> {
        debugln!("define `{}`", name.value);
        Ok(())
    }
}
