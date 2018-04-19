// Copyright (c) 2018 Fabian Schuiki

use ty2::basetypes::*;
use ty2::subtypes::*;
use ty2::types::*;

make_arenas!(
    /// An arena to allocate types nodes into.
    pub struct TypeArena<'t> {
        integer_basetype: IntegerBasetype,
        integer_subtype: IntegerSubtype<'t>,
        universal_integer: UniversalIntegerType,
    }
);
