// Copyright (c) 2018 Fabian Schuiki

use std::fmt;

use crate::common::score::Result;
use crate::common::source::{Span, Spanned};

use crate::hir::visit::Visitor;
use crate::score::ResolvableName;

/// Construct something from an AST node.
pub trait FromAst<'t>: Sized {
    type AllocInput: 't;
    type LatentInput: 't;
    type Context: 't;
    type Latent;

    /// Schedule construction of an HIR node from an AST node.
    ///
    /// This function performs initial setup, e.g. name declaration in the
    /// context, and then creates a `Slot` that constructs a ndoe of type `Self`
    /// on demand.
    fn alloc_slot(input: Self::AllocInput, context: Self::Context) -> Result<Self::Latent>;

    /// Construct an HIR node from an AST node.
    fn from_ast(input: Self::LatentInput, context: Self::Context) -> Result<Self>;
}

/// Common functions of HIR nodes.
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

/// Common functions of declaration HIR node.
pub trait Decl2<'t>: Node<'t> {
    /// The name of the declared item.
    fn name(&self) -> Spanned<ResolvableName>;
}

impl<'a, T: Decl2<'a>> From<&'a T> for &'a Decl2<'a> {
    fn from(t: &'a T) -> &'a Decl2<'a> {
        t
    }
}
