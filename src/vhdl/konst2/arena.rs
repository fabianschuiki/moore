// Copyright (c) 2018 Fabian Schuiki

#![allow(missing_docs)]

use std::borrow::Cow;

use arenas::{Alloc, AllokOwned};
use konst2::*;

make_arenas!(
    /// An arena to allocate constant values into.
    pub struct ConstArena<'t> {
        integer: IntegerConst<'t>,
    }
);

pub trait DummyAlloc<'s, 't, T> {
    fn dummy(&'s self, value: T) -> &'t mut T;
}

impl<'a, 't> DummyAlloc<'a, 'a, IntegerConst<'t>> for ConstArena<'t> {
    fn dummy(&'a self, value: IntegerConst<'t>) -> &'a mut IntegerConst<'t> {
        self.alloc(value)
    }
}

/// Allocate a constant.
pub trait AllocConst<'a, 't> {
    /// Allocate a constant.
    ///
    /// The lifetime of the result is tied to `Self`.
    fn alloc_const(&'a self, value: OwnedConst<'t>) -> &'t Const2<'t>;

    fn maybe_alloc_const(&'a self, value: Cow<'t, Const2<'t>>) -> &'t Const2<'t> {
        match value {
            Cow::Borrowed(x) => x,
            Cow::Owned(x) => self.alloc_const(x),
        }
    }

    fn force_alloc_const(&'a self, value: Cow<Const2<'t>>) -> &'t Const2<'t> {
        self.alloc_const(value.into_owned())
    }
}

impl<'t> AllocConst<'t, 't> for ConstArena<'t> {
    fn alloc_const(&'t self, value: OwnedConst<'t>) -> &'t Const2<'t> {
        match value {
            OwnedConst::Integer(k) => self.alloc(k),
        }
    }
}

impl<'t> AllokOwned<'t, 't, Const2<'t>> for ConstArena<'t> {
    fn allok_owned(&'t self, value: OwnedConst<'t>) -> &'t mut Const2<'t> {
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
