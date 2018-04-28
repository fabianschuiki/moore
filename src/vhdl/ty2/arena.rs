// Copyright (c) 2018 Fabian Schuiki

use arenas::{Alloc, AllocOwned};
use ty2::prelude::*;
use ty2::types::{NullType, UniversalRealType};
use ty2::ints::*;
use ty2::enums::*;
use ty2::physical::*;

make_arenas!(
    /// An arena to allocate types nodes into.
    pub struct TypeArena<'t> {
        integer_basetype: IntegerBasetype,
        integer_subtype: IntegerSubtype<'t>,
        enum_basetype: EnumBasetype,
        enum_subtype: EnumSubtype<'t>,
        physical_basetype: PhysicalBasetype,
        physical_subtype: PhysicalSubtype<'t>,
    }
);

impl<'t> AllocOwned<'t, 't, Type> for TypeArena<'t> {
    fn alloc_owned(&'t self, value: OwnedType<'t>) -> &'t Type {
        match value {
            OwnedType::IntegerBasetype(t) => self.alloc(t),
            OwnedType::IntegerSubtype(t) => self.alloc(t),
            OwnedType::EnumBasetype(t) => self.alloc(t),
            OwnedType::EnumSubtype(t) => self.alloc(t),
            OwnedType::PhysicalBasetype(t) => self.alloc(t),
            OwnedType::PhysicalSubtype(t) => self.alloc(t),
            OwnedType::Null => &NullType,
            OwnedType::UniversalInteger => &UniversalIntegerType,
            OwnedType::UniversalReal => &UniversalRealType,
        }
    }
}
