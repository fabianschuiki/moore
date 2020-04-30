// Copyright (c) 2016-2020 Fabian Schuiki

//! Dealing with types in an abstract manner.

use std::borrow::Borrow;
use std::fmt::{self, Debug, Display};

pub use num::BigInt;

use crate::ty2::access::*;
use crate::ty2::enums::*;
use crate::ty2::floats::*;
use crate::ty2::ints::*;
use crate::ty2::physical::*;

/// An interface for dealing with types.
///
/// This is the main type trait, which all types and subtypes implement.
pub trait Type: Debug + Display {
    /// Check if this is a scalar type.
    ///
    /// Enumeration, integer, floating-point, and physical types are scalar.
    fn is_scalar(&self) -> bool;

    /// Check if this is a discrete type.
    ///
    /// Enumeration and integer types are discrete.
    fn is_discrete(&self) -> bool;

    /// Check if this is a numeric type.
    ///
    /// Integer, floating-point, and physical types are numeric.
    fn is_numeric(&self) -> bool;

    /// Check if this is a composite type.
    ///
    /// Array and record types are composite.
    fn is_composite(&self) -> bool;

    /// Convert into an owned type.
    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a;

    /// Clone this type.
    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a;

    /// Converts from `&Type` to `AnyType`.
    fn as_any(&self) -> AnyType;

    /// Check if two types are equal.
    fn is_equal(&self, other: &Type) -> bool {
        self.as_any() == other.as_any()
    }

    /// Check if the type can be implicitly cast to another.
    fn is_implicitly_castable(&self, _into: &Type) -> bool {
        false
    }
}

impl<'a> PartialEq for Type + 'a {
    fn eq(&self, other: &Type) -> bool {
        self.is_equal(other)
    }
}

impl<'a> Eq for Type + 'a {}

impl<'t> ToOwned for Type + 't {
    type Owned = OwnedType<'t>;

    fn to_owned(&self) -> OwnedType<'t> {
        Type::to_owned(self)
    }
}

/// A type.
///
/// This enum represents one of the types declared in this module. It is useful
/// in code that needs to know exactly what type it is operating on, for example
/// in a match expression. This is the root of the entire type system. If a user
/// declares a type, this enum carries the information as to which type was
/// declared.
#[derive(Copy, Clone, PartialEq)]
#[allow(missing_docs)]
pub enum AnyType<'t> {
    Enum(&'t EnumType),
    Integer(&'t IntegerType),
    Floating(&'t FloatingType),
    Physical(&'t PhysicalType),
    Array(&'t ArrayType<'t>),
    // record
    // access
    Access(&'t AccessType<'t>),
    // file
    // protected

    // Non-standard types.
    Null,
    UniversalInteger,
    UniversalReal,
    // subprogram
}

impl<'t> Display for AnyType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(self.as_type(), f)
    }
}

impl<'t> Debug for AnyType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Debug::fmt(self.as_type(), f)
    }
}

// impl<'t, T: Type> From<&'t T> for AnyType<'t> {
//     fn from(ty: &'t T) -> AnyType<'t> {
//         ty.as_any()
//     }
// }

impl<'t> AnyType<'t> {
    /// Perform type erasure.
    pub fn as_type(self) -> &'t Type {
        match self {
            AnyType::Enum(t) => t.as_type(),
            AnyType::Integer(t) => t.as_type(),
            AnyType::Floating(t) => t.as_type(),
            AnyType::Physical(t) => t.as_type(),
            AnyType::Array(t) => t,
            AnyType::Access(t) => t,
            AnyType::Null => &NullType,
            AnyType::UniversalInteger => &UniversalIntegerType,
            AnyType::UniversalReal => &UniversalRealType,
        }
    }

    /// Returns `Some(t)` if the type is `Enum(t)`, `None` otherwise.
    pub fn as_enum(self) -> Option<&'t EnumType> {
        match self {
            AnyType::Enum(t) => Some(t),
            _ => None,
        }
    }

    /// Returns `Some(t)` if the type is `Integer(t)`, `None` otherwise.
    pub fn as_integer(self) -> Option<&'t IntegerType> {
        match self {
            AnyType::Integer(t) => Some(t),
            _ => None,
        }
    }

    /// Returns `Some(t)` if the type is `Floating(t)`, `None` otherwise.
    pub fn as_floating(self) -> Option<&'t FloatingType> {
        match self {
            AnyType::Floating(t) => Some(t),
            _ => None,
        }
    }

    /// Returns `Some(t)` if the type is `Physical(t)`, `None` otherwise.
    pub fn as_physical(self) -> Option<&'t PhysicalType> {
        match self {
            AnyType::Physical(t) => Some(t),
            _ => None,
        }
    }

    /// Returns `Some(t)` if the type is `Array(t)`, `None` otherwise.
    pub fn as_array(self) -> Option<&'t ArrayType<'t>> {
        match self {
            AnyType::Array(t) => Some(t),
            _ => None,
        }
    }

    /// Returns `Some(t)` if the type is `Access(t)`, `None` otherwise.
    pub fn as_access(self) -> Option<&'t AccessType<'t>> {
        match self {
            AnyType::Access(t) => Some(t),
            _ => None,
        }
    }

    /// Checks if the type is `Null`.
    pub fn is_null(self) -> bool {
        match self {
            AnyType::Null => true,
            _ => false,
        }
    }

    /// Checks if the type is `UniversalInteger`.
    pub fn is_universal_integer(self) -> bool {
        match self {
            AnyType::UniversalInteger => true,
            _ => false,
        }
    }

    /// Checks if the type is `UniversalReal`.
    pub fn is_universal_real(self) -> bool {
        match self {
            AnyType::UniversalReal => true,
            _ => false,
        }
    }

    /// Returns an `&EnumType` or panics if the type is not `Enum`.
    pub fn unwrap_enum(self) -> &'t EnumType {
        self.as_enum().expect("type is not an enum type")
    }

    /// Returns an `&IntegerType` or panics if the type is not `Integer`.
    pub fn unwrap_integer(self) -> &'t IntegerType {
        self.as_integer().expect("type is not an integer type")
    }

    /// Returns an `&FloatingType` or panics if the type is not `Floating`.
    pub fn unwrap_floating(self) -> &'t FloatingType {
        self.as_floating()
            .expect("type is not a floating-point type")
    }

    /// Returns an `&PhysicalType` or panics if the type is not `Physical`.
    pub fn unwrap_physical(self) -> &'t PhysicalType {
        self.as_physical().expect("type is not a physical type")
    }

    /// Returns an `&ArrayType` or panics if the type is not `Array`.
    pub fn unwrap_array(self) -> &'t ArrayType<'t> {
        self.as_array().expect("type is not an array type")
    }

    /// Returns an `&AccessType` or panics if the type is not `Access`.
    pub fn unwrap_access(self) -> &'t AccessType<'t> {
        self.as_access().expect("type is not an access type")
    }

    /// Check if this is a scalar type.
    pub fn is_scalar(&self) -> bool {
        self.as_type().is_scalar()
    }

    /// Check if this is a discrete type.
    pub fn is_discrete(&self) -> bool {
        self.as_type().is_discrete()
    }

    /// Check if this is a numeric type.
    pub fn is_numeric(&self) -> bool {
        self.as_type().is_numeric()
    }

    /// Check if this is a composite type.
    pub fn is_composite(&self) -> bool {
        self.as_type().is_composite()
    }

    /// Clone this type.
    pub fn to_owned(&self) -> OwnedType<'t> {
        self.as_type().to_owned()
    }
}

/// An owned type.
#[derive(Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum OwnedType<'t> {
    EnumBasetype(EnumBasetype),
    EnumSubtype(EnumSubtype<'t>),
    IntegerBasetype(IntegerBasetype),
    IntegerSubtype(IntegerSubtype<'t>),
    FloatingBasetype(FloatingBasetype),
    FloatingSubtype(FloatingSubtype<'t>),
    PhysicalBasetype(PhysicalBasetype),
    PhysicalSubtype(PhysicalSubtype<'t>),
    Access(AccessType<'t>),
    Null,
    UniversalInteger,
    UniversalReal,
}

impl<'t> Borrow<Type + 't> for OwnedType<'t> {
    fn borrow(&self) -> &(Type + 't) {
        match *self {
            OwnedType::EnumBasetype(ref k) => k,
            OwnedType::EnumSubtype(ref k) => k,
            OwnedType::IntegerBasetype(ref k) => k,
            OwnedType::IntegerSubtype(ref k) => k,
            OwnedType::FloatingBasetype(ref k) => k,
            OwnedType::FloatingSubtype(ref k) => k,
            OwnedType::PhysicalBasetype(ref k) => k,
            OwnedType::PhysicalSubtype(ref k) => k,
            OwnedType::Access(ref k) => k,
            OwnedType::Null => &NullType,
            OwnedType::UniversalInteger => &UniversalIntegerType,
            OwnedType::UniversalReal => &UniversalRealType,
        }
    }
}

impl<'t> Display for OwnedType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Type as Display>::fmt(self.borrow(), f)
    }
}

impl<'t> Debug for OwnedType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Type as Debug>::fmt(self.borrow(), f)
    }
}

/// An array type.
#[derive(Debug, Clone, PartialEq)]
pub struct ArrayType<'t> {
    /// The index subtypes.
    indices: Vec<&'t Type>,
    /// The element subtype.
    element: &'t Type,
}

impl<'t> Type for ArrayType<'t> {
    fn is_scalar(&self) -> bool {
        false
    }

    fn is_discrete(&self) -> bool {
        false
    }

    fn is_numeric(&self) -> bool {
        false
    }

    fn is_composite(&self) -> bool {
        true
    }

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        unimplemented!()
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        unimplemented!()
    }

    fn as_any(&self) -> AnyType {
        AnyType::Array(self)
    }
}

impl<'t> Display for ArrayType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "array")?;
        Ok(())
    }
}

/// A null type.
///
/// This type is not strictly part of the VHDL type system. Rather, arrays that
/// have negative length degenerate into null arrays. We handle these types
/// explicitly, since they significantly change how types match.
///
/// # Example
///
/// ```
/// use moore_vhdl::ty2::{Type, NullType};
///
/// let ty = NullType;
///
/// assert_eq!(format!("{}", ty), "null");
/// assert_eq!(ty.is_scalar(), false);
/// assert_eq!(ty.is_discrete(), false);
/// assert_eq!(ty.is_numeric(), false);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct NullType;

impl Type for NullType {
    fn is_scalar(&self) -> bool {
        false
    }

    fn is_discrete(&self) -> bool {
        false
    }

    fn is_numeric(&self) -> bool {
        false
    }

    fn is_composite(&self) -> bool {
        false
    }

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::Null
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::Null
    }

    fn as_any(&self) -> AnyType {
        AnyType::Null
    }
}

impl Display for NullType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "null")
    }
}
