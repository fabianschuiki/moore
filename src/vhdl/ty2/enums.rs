// Copyright (c) 2018 Fabian Schuiki

//! Enumeration types.

use std::fmt::{self, Display};
use std::iter::{once, repeat};

pub use num::BigInt;

use common::name::{get_name_table, Name};
use ty2::prelude::*;
use ty2::ScalarSubtype;

/// An enumeration type.
///
/// This can either be an `EnumBasetype` or an `EnumSubtype`.
pub trait EnumType: Type {
    /// Convert to a type.
    fn as_type(&self) -> &Type;

    /// The literals of this enumeration type.
    fn literals(&self) -> &[EnumLiteral];

    /// The range of literals this type can assume.
    ///
    /// This is used to support subtyping of enumerations, where a subtype might
    /// only accept a subrange of the original literals.
    fn range(&self) -> Range<usize>;

    /// The base type of this enumeration.
    fn base_type(&self) -> &Type;

    /// The resolution function associated with this type.
    fn resolution_func(&self) -> Option<usize> {
        None
    }

    /// Returns `Some` if self is an `EnumBasetype`, `None` otherwise.
    fn as_basetype(&self) -> Option<&EnumBasetype> {
        None
    }

    /// Returns `Some` if self is an `EnumSubtype`, `None` otherwise.
    fn as_subtype(&self) -> Option<&EnumSubtype> {
        None
    }

    /// Returns an `&EnumBasetype` or panics if the type is not a basetype.
    fn unwrap_basetype(&self) -> &EnumBasetype {
        self.as_basetype()
            .expect("enumeration type is not a basetype")
    }

    /// Returns an `&EnumSubtype` or panics if the type is not a subtype.
    fn unwrap_subtype(&self) -> &EnumSubtype {
        self.as_subtype()
            .expect("enumeration type is not a subtype")
    }

    /// Check if two enumeration types are equal.
    fn is_equal(&self, other: &EnumType) -> bool;
}

impl<'t> PartialEq for EnumType + 't {
    fn eq(&self, other: &EnumType) -> bool {
        EnumType::is_equal(self, other)
    }
}

impl<'t> Eq for EnumType + 't {}

macro_rules! common_type_impl {
    () => {
        fn is_scalar(&self) -> bool {
            true
        }

        fn is_discrete(&self) -> bool {
            true
        }

        fn is_numeric(&self) -> bool {
            false
        }

        fn is_composite(&self) -> bool {
            false
        }

        fn as_any(&self) -> AnyType {
            AnyType::Enum(self)
        }
    }
}

/// An enumeration base type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumBasetype {
    /// The enumeration literals.
    lits: Vec<EnumLiteral>,
}

impl EnumBasetype {
    /// Create a new enumeration type.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{Type, EnumBasetype};
    ///
    /// let ty = EnumBasetype::new(vec![
    ///     "first".into(),
    ///     "second".into(),
    ///     '0'.into(),
    ///     '1'.into(),
    /// ]);
    ///
    /// assert_eq!(format!("{}", ty), "(first, second, '0', '1')");
    /// ```
    pub fn new<I: IntoIterator<Item = EnumLiteral>>(lits: I) -> EnumBasetype {
        EnumBasetype {
            lits: lits.into_iter().collect(),
        }
    }
}

impl Type for EnumBasetype {
    common_type_impl!();

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::EnumBasetype(self)
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::EnumBasetype(self.clone())
    }
}

impl EnumType for EnumBasetype {
    fn as_type(&self) -> &Type {
        self
    }

    fn literals(&self) -> &[EnumLiteral] {
        &self.lits
    }

    fn range(&self) -> Range<usize> {
        Range::ascending(0usize, self.lits.len())
    }

    fn base_type(&self) -> &Type {
        self
    }

    fn as_basetype(&self) -> Option<&EnumBasetype> {
        Some(self)
    }

    fn is_equal(&self, other: &EnumType) -> bool {
        other.as_basetype().map(|t| self == t).unwrap_or(false)
    }
}

impl Display for EnumBasetype {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;
        for (sep, lit) in once("").chain(repeat(", ")).zip(self.lits.iter()) {
            write!(f, "{}{}", sep, lit)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

/// A subtype of an enumeration type.
pub type EnumSubtype<'t> = ScalarSubtype<'t, EnumType, usize>;

impl<'t> EnumSubtype<'t> {
    /// Create a new enumeration subtype.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{Type, TypeMark, EnumBasetype, EnumSubtype, Range};
    /// use moore_vhdl::common::name::get_name_table;
    ///
    /// let ty = EnumBasetype::new(vec![
    ///     "first".into(),
    ///     "second".into(),
    ///     '0'.into(),
    ///     '1'.into(),
    /// ]);
    /// let tm = TypeMark::new(
    ///     get_name_table().intern("MY_TYPE", false),
    ///     &ty,
    /// );
    /// let subty = EnumSubtype::new(&tm, Range::ascending(1usize, 2usize)).unwrap();
    ///
    /// assert_eq!(format!("{}", subty), "MY_TYPE range second to '0'");
    /// ```
    pub fn new(mark: &'t TypeMark<'t>, range: Range<usize>) -> Option<EnumSubtype<'t>> {
        let base = mark.as_any().unwrap_enum();
        let base_range = base.range();
        if base_range.has_subrange(&range) {
            Some(EnumSubtype {
                resfn: None,
                mark: mark,
                base: base,
                con: range,
            })
        } else {
            None
        }
    }
}

impl<'t> Type for EnumSubtype<'t> {
    common_type_impl!();

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::EnumSubtype(self)
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::EnumSubtype(self.clone())
    }
}

impl<'t> EnumType for EnumSubtype<'t> {
    fn as_type(&self) -> &Type {
        self
    }

    fn literals(&self) -> &[EnumLiteral] {
        self.base.literals()
    }

    fn range(&self) -> Range<usize> {
        self.con
    }

    fn base_type(&self) -> &Type {
        self.base.as_type()
    }

    fn as_subtype(&self) -> Option<&EnumSubtype> {
        Some(self)
    }

    fn is_equal(&self, other: &EnumType) -> bool {
        other.as_subtype().map(|t| self == t).unwrap_or(false)
    }
}

impl<'t> Display for EnumSubtype<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} range {} {} {}",
            self.mark,
            self.base.literals()[*self.con.left()],
            self.con.dir(),
            self.base.literals()[*self.con.right()],
        )
    }
}

/// An enumeration literal.
///
/// Distinguishes between:
/// - identifier literals such as `FOO`, and
/// - character literals such as `'0'`.
#[derive(Debug, Clone, PartialEq, Eq)]
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
