// Copyright (c) 2018 Fabian Schuiki

use ty2::ints::*;
use ty2::enums::*;

make_arenas!(
    /// An arena to allocate types nodes into.
    pub struct TypeArena<'t> {
        integer_basetype: IntegerBasetype,
        integer_subtype: IntegerSubtype<'t>,
        enum_basetype: EnumBasetype,
        enum_subtype: EnumSubtype<'t>,
    }
);
