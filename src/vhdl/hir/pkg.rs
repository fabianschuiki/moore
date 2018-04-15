// Copyright (c) 2018 Fabian Schuiki

//! Packages

#![allow(dead_code)]

use std;
use std::fmt;
use std::cell::RefCell;

use common::{NodeId, SessionContext};
use common::name::Name;
use common::source::{Span, Spanned};

use arenas::{Alloc, AllocInto};
use syntax::ast;
use score::ResolvableName;
use scope2::{Def2, ScopeContext, ScopeData};

pub type Result<T> = std::result::Result<T, ()>;

make_arenas!(
    pub struct Arenas2<'t> {
        package:   Package2<'t>,
        type_decl: TypeDecl2,
        package_slot: Slot<'t, Package2<'t>>,
        type_decl_slot: Slot<'t, TypeDecl2>,
        scope_data: ScopeData<'t>,
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

impl<'t, T, L> LatentNode<L> for Slot<'t, T>
where
    &'t T: Into<L>,
    T: FromAst<'t>,
    T::Context: AllocInto<'t, T> + Clone,
{
    fn poll(&self) -> Result<L> {
        Slot::poll(self).map(|n| n.into())
    }
}

impl<'t, T> fmt::Debug for Slot<'t, T>
where
    T: FromAst<'t>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self.0.borrow() {
            SlotState::Fresh(..) => write!(f, "Slot(Fresh)"),
            SlotState::ReadyOk(..) => write!(f, "Slot(ReadyOk)"),
            SlotState::ReadyErr => write!(f, "Slot(ReadyErr)"),
        }
    }
}

pub struct Package2<'t> {
    id: NodeId,
    span: Span,
    name: Spanned<Name>,
    decls: Vec<&'t LatentNode<&'t Decl2>>,
}

impl<'t> Package2<'t> {
    pub fn decls(&self) -> &[&'t LatentNode<&'t Decl2>] {
        &self.decls
    }
}

impl<'t> FromAst<'t> for Package2<'t> {
    type Input = &'t ast::PkgDecl;
    type Context = Context<'t>;

    fn alloc_slot(ast: Self::Input, context: Self::Context) -> Result<&'t Slot<'t, Self>> {
        let slot = context.alloc(Slot::new(ast, context));
        context.define(ast.name.map(Into::into), Def2::Pkg(slot))?;
        Ok(slot)
    }

    fn from_ast(ast: Self::Input, context: Self::Context) -> Result<Self> {
        debugln!("create package decl {}", ast.name.value);
        let context = context.subscope();
        let decls = ast.decls
            .iter()
            .flat_map(|decl| -> Option<&'t LatentNode<&'t Decl2>> {
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

impl<'t> Decl2 for Package2<'t> {
    fn name(&self) -> Spanned<ResolvableName> {
        self.name.map(Into::into)
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

impl Decl2 for TypeDecl2 {
    fn name(&self) -> Spanned<ResolvableName> {
        self.name.map(Into::into)
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

impl<'a, T: Node> From<&'a T> for &'a Node {
    fn from(t: &'a T) -> &'a Node {
        t
    }
}

/// Lazily resolve to a `Node`.
pub trait LatentNode<T> {
    /// Access the underlying node.
    ///
    /// On the first time this function is called, the node is created.
    /// Subsequent calls are guaranteed to return the same node. Node creation
    /// may fail for a variety of reasons, thus the function returns a `Result`.
    fn poll(&self) -> Result<T>;
}

pub trait Decl2: Node {
    /// The name of the declared item.
    fn name(&self) -> Spanned<ResolvableName>;
}

impl<'a, T: Decl2> From<&'a T> for &'a Decl2 {
    fn from(t: &'a T) -> &'a Decl2 {
        t
    }
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
    pub sess: &'t SessionContext,
    pub arenas: &'t Arenas2<'t>,
    pub scope: &'t ScopeData<'t>,
}

impl<'t> Context<'t> {
    pub fn subscope(&self) -> Context<'t> {
        Context {
            scope: self.arenas.alloc(ScopeData::new(self.scope)),
            ..*self
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

impl<'t> ScopeContext<'t> for Context<'t> {
    fn define(&self, name: Spanned<ResolvableName>, def: Def2<'t>) -> Result<()> {
        self.scope.define(name, def, self.sess)
    }

    fn import_def(&self, name: Spanned<ResolvableName>, def: Def2<'t>) -> Result<()> {
        self.scope.import_def(name, def)
    }

    fn import_scope(&self, scope: &'t ScopeData<'t>) -> Result<()> {
        self.scope.import_scope(scope)
    }
}
