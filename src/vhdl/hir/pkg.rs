// Copyright (c) 2018 Fabian Schuiki

//! Packages

#![allow(dead_code)]

use std;
use std::fmt;
use std::cell::RefCell;

use common::{NodeId, SessionContext};
use common::name::Name;
use common::source::{Span, Spanned};
use common::errors::*;

use arenas::{Alloc, AllocInto};
use syntax::ast;
use score::ResolvableName;
use scope2::{Def2, ScopeContext, ScopeData};
use hir::visit::Visitor;
use hir::Library;

pub type Result<T> = std::result::Result<T, ()>;

make_arenas!(
    pub struct Arenas2<'t> {
        library: Library<'t>,
        package: Package2<'t>,
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
    Transient,
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
            SlotState::Transient => panic!("slot recursion"),
            _ => (),
        }
        let (ast, context) = match self.0.replace(SlotState::Transient) {
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

impl<'t, T, L> LatentNode<'t, L> for Slot<'t, T>
where
    &'t T: Into<&'t L>,
    L: ?Sized + 't,
    T: FromAst<'t> + Node<'t>,
    T::Context: AllocInto<'t, T> + Clone,
{
    fn poll(&self) -> Result<&'t L> {
        Slot::poll(self).map(|n| n.into())
    }

    fn accept(&self, visitor: &mut Visitor<'t>) {
        match self.poll() {
            Ok(n) => n.accept(visitor),
            Err(()) => (),
        }
    }

    fn walk(&self, visitor: &mut Visitor<'t>) {
        match self.poll() {
            Ok(n) => n.walk(visitor),
            Err(()) => (),
        }
    }
}

impl<'t, T> fmt::Debug for Slot<'t, T>
where
    T: FromAst<'t>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self.0.borrow() {
            SlotState::Fresh(..) => write!(f, "Slot(Fresh)"),
            SlotState::Transient => write!(f, "Slot(Transient)"),
            SlotState::ReadyOk(..) => write!(f, "Slot(ReadyOk)"),
            SlotState::ReadyErr => write!(f, "Slot(ReadyErr)"),
        }
    }
}

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
    type Context = Context<'t>;

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
                    ast::DeclItem::PkgDecl(ref decl) => {
                        Some(Package2::alloc_slot(decl, context).ok()?)
                    }
                    ast::DeclItem::TypeDecl(ref decl) => {
                        Some(TypeDecl2::alloc_slot(decl, context).ok()?)
                    }
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

pub trait AnyScope {}

pub trait Node<'t>: fmt::Debug {
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

    /// Accept a visitor and call its corresponding `visit_*` function.
    fn accept(&'t self, visitor: &mut Visitor<'t>);

    /// Walk a visitor over the node's subtree.
    fn walk(&'t self, visitor: &mut Visitor<'t>);
}

impl<'a, T: Node<'a>> From<&'a T> for &'a Node<'a> {
    fn from(t: &'a T) -> &'a Node<'a> {
        t
    }
}

/// Lazily resolve to a `Node`.
pub trait LatentNode<'t, T: 't + ?Sized>: fmt::Debug {
    /// Access the underlying node.
    ///
    /// On the first time this function is called, the node is created.
    /// Subsequent calls are guaranteed to return the same node. Node creation
    /// may fail for a variety of reasons, thus the function returns a `Result`.
    fn poll(&self) -> Result<&'t T>;

    /// Accept a visitor.
    ///
    /// Polls the latent node and if successful calls `accept()` on it.
    fn accept(&self, visitor: &mut Visitor<'t>);

    /// Walk a visitor over the latent node's subtree.
    ///
    /// Polls the latent node and if successful calls `walk()` on it.
    fn walk(&self, visitor: &mut Visitor<'t>);
}

pub trait Decl2<'t>: Node<'t> {
    /// The name of the declared item.
    fn name(&self) -> Spanned<ResolvableName>;
}

impl<'a, T: Decl2<'a>> From<&'a T> for &'a Decl2<'a> {
    fn from(t: &'a T) -> &'a Decl2<'a> {
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
    /// Create a subscope and return a new context for that scope.
    pub fn create_subscope(&self) -> Context<'t> {
        Context {
            scope: self.arenas.alloc(ScopeData::new(self.scope)),
            ..*self
        }
    }

    /// Return the current scope.
    pub fn scope(&self) -> &'t ScopeData<'t> {
        self.scope
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

    fn import_def(&self, name: ResolvableName, def: Spanned<Def2<'t>>) -> Result<()> {
        self.scope.import_def(name, def)
    }

    fn import_scope(&self, scope: &'t ScopeData<'t>) -> Result<()> {
        self.scope.import_scope(scope)
    }

    fn resolve(&self, name: ResolvableName, recur: bool) -> Vec<Spanned<Def2<'t>>> {
        self.scope.resolve(name, recur)
    }
}

impl<'t> DiagEmitter for Context<'t> {
    fn emit(&self, diag: DiagBuilder2) {
        self.sess.emit(diag)
    }
}

pub fn apply_use_clauses<'a, I>(clauses: I, context: Context)
where
    I: IntoIterator<Item = &'a ast::CompoundName>,
{
    for u in clauses.into_iter() {
        let e = apply_use_clause(u, context);
        std::mem::forget(e);
    }
}

fn apply_use_clause(clause: &ast::CompoundName, context: Context) -> Result<()> {
    debugln!("apply use {}", clause.span.extract());

    // Lookup the primary name.
    let pn = ResolvableName::from_primary_name(&clause.primary, context)?;
    let mut lookup = context.resolve(pn.value, true);
    let mut lookup_name = pn;
    if lookup.is_empty() {
        context.emit(DiagBuilder2::error(format!("`{}` is unknown", pn.value)).span(pn.span));
        return Err(());
    }
    // debugln!("`{}` resolved to {:?}", pn.value, lookup);

    // Process the name parts.
    for part in &clause.parts {
        // Ensure the name is unique.
        if lookup.len() > 1 {
            let mut d = DiagBuilder2::error(format!("`{}` is ambiguous", lookup_name.value))
                .span(lookup_name.span)
                .add_note("Refers to the following:");
            for l in lookup {
                d = d.span(l.span);
            }
            context.emit(d);
            return Err(());
        }
        let def = lookup.into_iter().next().unwrap();
        let scope = match def.value {
            Def2::Lib(x) => x.scope(),
            Def2::Pkg(x) => x.poll()?.scope(),
            _ => {
                context.emit(
                    DiagBuilder2::error(format!("cannot select into {}", def.value.desc_kind()))
                        .span(def.span),
                );
                return Err(());
            }
        };

        // Perform the operation that the name part requests.
        match *part {
            ast::NamePart::Select(ref primary) => {
                lookup_name = ResolvableName::from_primary_name(primary, context)?;
                lookup = scope.resolve(lookup_name.value, false);
                // debugln!("`{}` resolved to {:?}", lookup_name.value, lookup);
                if lookup.is_empty() {
                    context.emit(
                        DiagBuilder2::error(format!("`{}` is unknown", lookup_name.value))
                            .span(lookup_name.span),
                    );
                    return Err(());
                }
            }
            ast::NamePart::SelectAll(..) => {
                context.import_scope(scope)?;
                return Ok(());
            }
            _ => {
                context.emit(
                    DiagBuilder2::error(format!("`{}` cannot be used", clause.span.extract()))
                        .span(clause.span),
                );
                return Err(());
            }
        }
    }

    debugln!("`{}` resolved to {:?}", clause.span.extract(), lookup);
    for l in lookup {
        context.import_def(lookup_name.value, l)?;
    }
    Ok(())
}
