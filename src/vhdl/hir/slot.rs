// Copyright (c) 2018 Fabian Schuiki

use std::fmt;
use std::cell::RefCell;

use common::score::Result;

use arenas::AllocInto;
use hir::visit::Visitor;
use hir::{FromAst, LatentNode, Node};

/// A placeholder for an HIR node.
pub struct Slot<'t, T>(RefCell<SlotState<'t, T>>)
where
    T: FromAst<'t> + 't;

#[derive(Copy, Clone)]
enum SlotState<'t, T>
where
    T: FromAst<'t> + 't,
{
    Fresh(T::LatentInput, T::Context),
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
    pub fn new(ast: T::LatentInput, context: T::Context) -> Slot<'t, T> {
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
