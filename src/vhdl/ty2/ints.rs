// Copyright (c) 2018 Fabian Schuiki

//! Integer types.

use std::fmt::{self, Display};
use std::ops::Deref;

pub use num::BigInt;

use ty2::{AnyType, Range, ScalarSubtype, Type, TypeMark};

/// An integer type.
///
/// This can either be an `IntegerBasetype` or an `IntegerSubtype`.
pub trait IntegerType: Type {
    /// Convert to a type.
    fn as_type(&self) -> &Type;

    /// The range of values this integer can assume.
    ///
    /// Universal integers return `None` here, as they do not have a value range
    /// associated with them.
    fn range(&self) -> Option<&Range<BigInt>>;

    /// The base type of this integer.
    fn base_type(&self) -> &Type;

    /// The resolution function associated with this type.
    fn resolution_func(&self) -> Option<usize> {
        None
    }

    /// Returns `Some` if self is an `IntegerBasetype`, `None` otherwise.
    fn as_basetype(&self) -> Option<&IntegerBasetype> {
        None
    }

    /// Returns `Some` if self is an `IntegerSubtype`, `None` otherwise.
    fn as_subtype(&self) -> Option<&IntegerSubtype> {
        None
    }

    /// Checks whether this is a universal integer type.
    fn is_universal(&self) -> bool {
        false
    }

    /// Returns an `&IntegerBasetype` or panics if the type is not a basetype.
    fn unwrap_basetype(&self) -> &IntegerBasetype {
        self.as_basetype().expect("integer type is not a basetype")
    }

    /// Returns an `&IntegerSubtype` or panics if the type is not a subtype.
    fn unwrap_subtype(&self) -> &IntegerSubtype {
        self.as_subtype().expect("integer type is not a subtype")
    }

    /// Check if two integer types are equal.
    fn is_equal(&self, other: &IntegerType) -> bool;
}

impl<'t, T> Type for T
where
    T: IntegerType + 't,
{
    fn is_scalar(&self) -> bool {
        true
    }
    fn is_discrete(&self) -> bool {
        true
    }
    fn is_numeric(&self) -> bool {
        true
    }
    fn is_composite(&self) -> bool {
        false
    }
    fn as_any(&self) -> AnyType {
        AnyType::Integer(self)
    }
}

impl<'t> PartialEq for IntegerType + 't {
    fn eq(&self, other: &IntegerType) -> bool {
        IntegerType::is_equal(self, other)
    }
}

impl<'t> Eq for IntegerType + 't {}

/// An integer base type.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct IntegerBasetype {
    /// The range of values.
    range: Range<BigInt>,
}

impl IntegerBasetype {
    /// Create a new integer type.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate moore_vhdl;
    /// # extern crate num;
    /// # fn main() {
    /// use moore_vhdl::ty2::{Type, IntegerBasetype, Range, RangeDir};
    /// use num::BigInt;
    ///
    /// let a = IntegerBasetype::new(Range::ascending(0, 42));
    /// let b = IntegerBasetype::new(Range::descending(42, 0));
    ///
    /// assert_eq!(format!("{}", a), "0 to 42");
    /// assert_eq!(format!("{}", b), "42 downto 0");
    /// assert_eq!(a.dir(), RangeDir::To);
    /// assert_eq!(b.dir(), RangeDir::Downto);
    /// assert_eq!(a.len(), BigInt::from(43));
    /// assert_eq!(b.len(), BigInt::from(43));
    /// # }
    /// ```
    pub fn new(range: Range<BigInt>) -> IntegerBasetype {
        IntegerBasetype { range: range }
    }
}

impl IntegerType for IntegerBasetype {
    fn as_type(&self) -> &Type {
        self
    }

    fn range(&self) -> Option<&Range<BigInt>> {
        Some(&self.range)
    }

    fn base_type(&self) -> &Type {
        self
    }

    fn as_basetype(&self) -> Option<&IntegerBasetype> {
        Some(self)
    }

    fn is_equal(&self, other: &IntegerType) -> bool {
        other.as_basetype().map(|t| self == t).unwrap_or(false)
    }
}

impl Deref for IntegerBasetype {
    type Target = Range<BigInt>;
    fn deref(&self) -> &Range<BigInt> {
        &self.range
    }
}

impl Display for IntegerBasetype {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.range)
    }
}

/// A subtype of an integer type.
pub type IntegerSubtype<'t> = ScalarSubtype<'t, IntegerType, BigInt>;

impl<'t> IntegerSubtype<'t> {
    /// Create a new integer subtype.
    ///
    /// Returns `Some(...)` if `range` is a subrange of the integer, or `None`
    /// otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{Type, TypeMark, IntegerBasetype, IntegerSubtype, Range};
    /// use moore_vhdl::common::name::get_name_table;
    ///
    /// let ty = IntegerBasetype::new(Range::ascending(0usize, 255usize));
    /// let tm = TypeMark::new(
    ///     get_name_table().intern("BYTE", false),
    ///     &ty,
    /// );
    /// let a = IntegerSubtype::new(&tm, Range::ascending(0usize, 15usize)).unwrap();
    /// let b = IntegerSubtype::new(&tm, Range::descending(15usize, 0usize)).unwrap();
    ///
    /// assert_eq!(format!("{}", a), "BYTE range 0 to 15");
    /// assert_eq!(format!("{}", b), "BYTE range 15 downto 0");
    /// ```
    pub fn new(mark: &'t TypeMark, range: Range<BigInt>) -> Option<IntegerSubtype<'t>> {
        let base = mark.as_any().unwrap_integer();
        let base_range = base.range()?;
        if base_range.has_subrange(&range) {
            Some(IntegerSubtype {
                resfn: base.resolution_func(),
                mark: mark,
                base: base,
                con: range,
            })
        } else {
            None
        }
    }
}

impl<'t> IntegerType for IntegerSubtype<'t> {
    fn as_type(&self) -> &Type {
        self
    }

    fn range(&self) -> Option<&Range<BigInt>> {
        Some(&self.con)
    }

    fn base_type(&self) -> &Type {
        self.mark
    }

    fn as_subtype(&self) -> Option<&IntegerSubtype> {
        Some(self)
    }

    fn is_equal(&self, other: &IntegerType) -> bool {
        other.as_subtype().map(|t| self == t).unwrap_or(false)
    }
}

impl<'t> Display for IntegerSubtype<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} range {}", self.mark, self.con)
    }
}
