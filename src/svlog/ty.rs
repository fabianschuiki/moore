// Copyright (c) 2016-2019 Fabian Schuiki

//! An implementation of the verilog type system.

use crate::crate_prelude::*;

/// A verilog type.
pub type Type<'t> = &'t TypeKind<'t>;

/// Type data.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TypeKind<'t> {
    /// The `void` type.
    Void,
    /// The `time` type.
    Time,
    /// A single bit type.
    Bit(Domain),
    /// An integer type.
    Int(usize, Domain),
    /// A named type.
    ///
    /// The first field represents how the type was originally named by the
    /// user. The second field represents the binding of the resolved name. The
    /// third field represents the actual type.
    Named(Spanned<Name>, NodeId, Type<'t>),
    /// A struct type.
    Struct(NodeId),
    /// A packed array type.
    PackedArray(usize, Type<'t>),
}

impl<'t> TypeKind<'t> {
    /// Check if this is the void type.
    pub fn is_void(&self) -> bool {
        match *self {
            TypeKind::Void => true,
            _ => false,
        }
    }

    /// Get the width of the type.
    ///
    /// Panics if the type is not an integer.
    pub fn width(&self) -> usize {
        match *self {
            TypeKind::Bit(_) => 1,
            TypeKind::Int(w, _) => w,
            TypeKind::Named(_, _, ty) => ty.width(),
            _ => panic!("{:?} has no width", self),
        }
    }
}

/// The number of values each bit of a type can assume.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Domain {
    /// Two-valued types such as `bit` or `int`.
    TwoValued,
    /// Four-valued types such as `logic` or `integer`.
    FourValued,
}

/// The `void` type.
pub static VOID_TYPE: TypeKind<'static> = TypeKind::Void;
/// The `time` type.
pub static TIME_TYPE: TypeKind<'static> = TypeKind::Time;
/// The `bit` type.
pub static BIT_TYPE: TypeKind<'static> = TypeKind::Bit(ty::Domain::TwoValued);
/// The `logic` type.
pub static LOGIC_TYPE: TypeKind<'static> = TypeKind::Bit(ty::Domain::FourValued);
