// Copyright (c) 2018 Fabian Schuiki

#![allow(missing_docs)]

use arenas::{Alloc, AllocOwned};
use konst2::*;

make_arenas!(
    /// An arena to allocate constant values into.
    pub struct ConstArena<'t> {
        integer: IntegerConst<'t>,
        floating: FloatingConst<'t>,
    }
);

impl<'t> AllocOwned<'t, 't, Const2<'t>> for ConstArena<'t> {
    fn alloc_owned(&'t self, value: OwnedConst<'t>) -> &'t Const2<'t> {
        match value {
            OwnedConst::Integer(k) => self.alloc(k),
            OwnedConst::Floating(k) => self.alloc(k),
        }
    }
}
