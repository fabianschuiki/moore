// Copyright (c) 2017-2018 Fabian Schuiki

//! The fundamental types.

use std::fmt::{self, Debug, Display};
use std::iter::{once, repeat};

use common::name::{get_name_table, Name};

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

    /// Converts from `&Type` to `AnyType`.
    fn as_any(&self) -> AnyType;
}

/// A type.
///
/// This enum represents one of the types declared in this module. It is useful
/// in code that needs to know exactly what type it is operating on, for example
/// in a match expression. This is the root of the entire type system. If a user
/// declares a type, this enum carries the information as to which type was
/// declared.
#[derive(Copy, Clone)]
pub enum AnyType<'t> {
    /// An enumeration type.
    Enum(&'t EnumType),
    // integer
    // float
    // physical
    // array
    // record
    // access
    // file
    // protected

    // Non-standard types.
    // null
    // universal integer
    // universal real
    // subprogram
}

impl<'t> Type for AnyType<'t> {
    fn is_scalar(&self) -> bool {
        match *self {
            AnyType::Enum(t) => t.is_scalar(),
        }
    }

    fn is_discrete(&self) -> bool {
        match *self {
            AnyType::Enum(t) => t.is_discrete(),
        }
    }

    fn is_numeric(&self) -> bool {
        match *self {
            AnyType::Enum(t) => t.is_numeric(),
        }
    }

    fn as_any(&self) -> AnyType {
        *self
    }
}

impl<'t> Display for AnyType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnyType::Enum(t) => Display::fmt(t, f),
        }
    }
}

impl<'t> Debug for AnyType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnyType::Enum(t) => Debug::fmt(t, f),
        }
    }
}

impl<'t, T: Type> From<&'t T> for AnyType<'t> {
    fn from(ty: &'t T) -> AnyType<'t> {
        ty.as_any()
    }
}

/// An enumeration type.
///
/// See IEEE 1076-2008 section 5.2.2.
#[derive(Debug)]
pub struct EnumType {
    /// The enumeration literals.
    lits: Vec<EnumLiteral>,
}

impl EnumType {
    /// Create a new enumeration type.
    ///
    /// ```
    /// use moore_vhdl::ty2::{Type, EnumType};
    ///
    /// let ty = EnumType::new(vec![
    ///     "first".into(),
    ///     "second".into(),
    ///     '0'.into(),
    ///     '1'.into(),
    /// ]);
    ///
    /// assert_eq!(format!("{}", ty), "(first, second, '0', '1')");
    /// assert_eq!(format!("{}", ty.as_any()), "(first, second, '0', '1')");
    /// ```
    pub fn new<I: IntoIterator<Item=EnumLiteral>>(lits: I) -> EnumType {
        EnumType {
            lits: lits.into_iter().collect(),
        }
    }

    /// Return the literals.
    pub fn literals(&self) -> &[EnumLiteral] {
        &self.lits
    }
}

impl Type for EnumType {
    fn is_scalar(&self) -> bool { true }
    fn is_discrete(&self) -> bool { true }
    fn is_numeric(&self) -> bool { false }
    fn as_any(&self) -> AnyType { AnyType::Enum(self) }
}

impl Display for EnumType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;
        for (sep, lit) in once("").chain(repeat(", ")).zip(self.lits.iter()) {
            write!(f, "{}{}", sep, lit)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

/// An enumeration literal.
///
/// Distinguishes between:
/// - identifier literals such as `FOO`, and
/// - character literals such as `'0'`.
#[derive(Debug)]
pub enum EnumLiteral {
    /// An identifier enumeration literal.
    Ident(Name),
    /// A character enumeration ltieral.
    Char(char),
}

impl<'a> From<&'a str> for EnumLiteral {
    fn from(n: &'a str) -> EnumLiteral {
        EnumLiteral::Ident(get_name_table().intern(n, false))
    }
}

impl From<Name> for EnumLiteral {
    fn from(n: Name) -> EnumLiteral {
        EnumLiteral::Ident(n)
    }
}

impl From<char> for EnumLiteral {
    fn from(c: char) -> EnumLiteral {
        EnumLiteral::Char(c)
    }
}

impl Display for EnumLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            EnumLiteral::Ident(n) => write!(f, "{}", n),
            EnumLiteral::Char(c) => write!(f, "'{}'", c),
        }
    }
}

/// A null type.
///
/// This type is not strictly part of the VHDL type system. Rather, arrays that
/// have negative length degenerate into null arrays. We handle these types
/// explicitly, since they significantly change how types match.
pub struct NullType;
