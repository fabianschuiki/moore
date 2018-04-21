// Copyright (c) 2018 Fabian Schuiki

#![allow(missing_docs)]

use std::borrow::Cow;

use arenas::Alloc;
use konst2::*;

make_arenas!(
    /// An arena to allocate constant values into.
    pub struct ConstArena<'t> {
        integer: IntegerConst<'t>,
    }
);

/// Allocate a constant.
pub trait AllocConst<'t> {
    /// Allocate a constant.
    ///
    /// The lifetime of the result is tied to `Self`.
    fn alloc_const<'a>(&'a self, value: OwnedConst<'t>) -> &'a Const2<'t>;

    fn maybe_alloc_const<'a>(&'a self, value: Cow<'a, Const2<'t>>) -> &'a Const2<'t> {
        match value {
            Cow::Borrowed(x) => x,
            Cow::Owned(x) => self.alloc_const(x),
        }
    }

    fn force_alloc_const<'a>(&'a self, value: Cow<Const2<'t>>) -> &'a Const2<'t> {
        self.alloc_const(value.into_owned())
    }
}

/// Allocate a constant into an arena.
pub trait AllocConstInto<'t> {
    /// Allocate a constant into an arena.
    fn alloc_const(&self, value: OwnedConst<'t>) -> &'t Const2<'t>;

    fn maybe_alloc_const(&self, value: Cow<'t, Const2<'t>>) -> &'t Const2<'t> {
        match value {
            Cow::Borrowed(x) => x,
            Cow::Owned(x) => self.alloc_const(x),
        }
    }

    fn force_alloc_const(&self, value: Cow<Const2<'t>>) -> &'t Const2<'t> {
        self.alloc_const(value.into_owned())
    }
}

impl<'t> AllocConst<'t> for ConstArena<'t> {
    fn alloc_const(&self, value: OwnedConst<'t>) -> &Const2<'t> {
        match value {
            OwnedConst::Integer(k) => self.alloc(k),
        }
    }
}

// pub trait Decow<'a, A> {
//     type Output;
//     fn alloc(self, arena: &A) -> Self::Output;
//     fn force_alloc(self, arena: &A) -> Self::Output;
// }

// impl<'a, 't> Decow<'a, AllocConst> for Cow<'a, Const2<'t>> {}
