// Copyright (c) 2017-2018 Fabian Schuiki

//! The fundamental types.

use std::fmt::{self, Debug, Display};
use std::iter::{once, repeat};
use std::ops::{Add, Sub, Deref};

pub use num::{BigInt, BigRational};
use num::One;

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
    /// An integer type.
    Integer(&'t IntegerType),
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
            AnyType::Enum(t)    => t.is_scalar(),
            AnyType::Integer(t) => t.is_scalar(),
        }
    }

    fn is_discrete(&self) -> bool {
        match *self {
            AnyType::Enum(t)    => t.is_discrete(),
            AnyType::Integer(t) => t.is_discrete(),
        }
    }

    fn is_numeric(&self) -> bool {
        match *self {
            AnyType::Enum(t)    => t.is_numeric(),
            AnyType::Integer(t) => t.is_numeric(),
        }
    }

    fn as_any(&self) -> AnyType {
        *self
    }
}

impl<'t> Display for AnyType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnyType::Enum(t)    => Display::fmt(t, f),
            AnyType::Integer(t) => Display::fmt(t, f),
        }
    }
}

impl<'t> Debug for AnyType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnyType::Enum(t)    => Debug::fmt(t, f),
            AnyType::Integer(t) => Debug::fmt(t, f),
        }
    }
}

impl<'t, T: Type> From<&'t T> for AnyType<'t> {
    fn from(ty: &'t T) -> AnyType<'t> {
        ty.as_any()
    }
}

/// An enumeration type.
#[derive(Debug)]
pub struct EnumType {
    /// The enumeration literals.
    lits: Vec<EnumLiteral>,
}

impl EnumType {
    /// Create a new enumeration type.
    ///
    /// # Example
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

/// An integer type.
#[derive(Debug)]
pub struct IntegerType {
    /// The range of values.
    range: Range<BigInt>,
}

impl IntegerType {
    /// Create a new integer type.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{Type, IntegerType, Range, RangeDir, BigInt};
    ///
    /// let a = IntegerType::new(Range::ascending(0, 42));
    /// let b = IntegerType::new(Range::descending(42, 0));
    ///
    /// assert_eq!(format!("{}", a), "0 to 42");
    /// assert_eq!(format!("{}", a.as_any()), "0 to 42");
    /// assert_eq!(format!("{}", b), "42 downto 0");
    /// assert_eq!(format!("{}", b.as_any()), "42 downto 0");
    /// assert_eq!(a.dir(), RangeDir::To);
    /// assert_eq!(b.dir(), RangeDir::Downto);
    /// assert_eq!(a.len(), BigInt::from(43));
    /// assert_eq!(b.len(), BigInt::from(43));
    /// ```
    pub fn new(range: Range<BigInt>) -> IntegerType {
        IntegerType {
            range: range,
        }
    }
}

impl Type for IntegerType {
    fn is_scalar(&self) -> bool { true }
    fn is_discrete(&self) -> bool { true }
    fn is_numeric(&self) -> bool { true }
    fn as_any(&self) -> AnyType { AnyType::Integer(self) }
}

impl Display for IntegerType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.range)
    }
}

impl Deref for IntegerType {
    type Target = Range<BigInt>;
    fn deref(&self) -> &Range<BigInt> {
        &self.range
    }
}

/// A directed range of values.
///
/// `Range<T>` has the same semantics as ranges in VHDL. They have a direction
/// associated with them, and left and right bounds. The range may be a null
/// range if the lower bound is greater than or equal to the upper bound.
#[derive(Debug, PartialEq, Eq)]
pub struct Range<T> {
    /// The direction.
    dir: RangeDir,
    /// The left bound.
    left: T,
    /// The right bound.
    right: T,
}

impl<T: Ord + One> Range<T> where for<'a> &'a T: Add<Output=T> + Sub<Output=T> {
    /// Create an ascending range.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::IntegerRange;
    ///
    /// let r = IntegerRange::ascending(0, 42);
    ///
    /// assert_eq!(format!("{}", r), "0 to 42");
    /// ```
    pub fn ascending<L,R>(left: L, right: R) -> Range<T> where T: From<L> + From<R> {
        Range {
            dir: RangeDir::To,
            left: left.into(),
            right: right.into(),
        }
    }

    /// Create a descending range.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::IntegerRange;
    ///
    /// let r = IntegerRange::descending(42, 0);
    ///
    /// assert_eq!(format!("{}", r), "42 downto 0");
    /// ```
    pub fn descending<L,R>(left: L, right: R) -> Range<T> where T: From<L> + From<R> {
        Range {
            dir: RangeDir::Downto,
            left: left.into(),
            right: right.into(),
        }
    }

    /// Return the direction of the range.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{IntegerRange, RangeDir};
    ///
    /// let a = IntegerRange::ascending(0, 42);
    /// let b = IntegerRange::descending(42, 0);
    ///
    /// assert_eq!(a.dir(), RangeDir::To);
    /// assert_eq!(b.dir(), RangeDir::Downto);
    /// ```
    pub fn dir(&self) -> RangeDir {
        self.dir
    }

    /// Return the left bound of the range.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{IntegerRange, BigInt};
    ///
    /// let a = IntegerRange::ascending(0, 42);
    /// let b = IntegerRange::descending(42, 0);
    ///
    /// assert_eq!(a.left(), &BigInt::from(0));
    /// assert_eq!(b.left(), &BigInt::from(42));
    /// ```
    pub fn left(&self) -> &T {
        &self.left
    }

    /// Return the right bound of the range.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{IntegerRange, BigInt};
    ///
    /// let a = IntegerRange::ascending(0, 42);
    /// let b = IntegerRange::descending(42, 0);
    ///
    /// assert_eq!(a.right(), &BigInt::from(42));
    /// assert_eq!(b.right(), &BigInt::from(0));
    /// ```
    pub fn right(&self) -> &T {
        &self.right
    }

    /// Return the lower bound of the range.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{IntegerRange, BigInt};
    ///
    /// let a = IntegerRange::ascending(0, 42);
    /// let b = IntegerRange::descending(42, 0);
    ///
    /// assert_eq!(a.lower(), &BigInt::from(0));
    /// assert_eq!(b.lower(), &BigInt::from(0));
    /// ```
    pub fn lower(&self) -> &T {
        match self.dir {
            RangeDir::To => &self.left,
            RangeDir::Downto => &self.right,
        }
    }

    /// Return the upper bound of the range.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{IntegerRange, BigInt};
    ///
    /// let a = IntegerRange::ascending(0, 42);
    /// let b = IntegerRange::descending(42, 0);
    ///
    /// assert_eq!(a.upper(), &BigInt::from(42));
    /// assert_eq!(b.upper(), &BigInt::from(42));
    /// ```
    pub fn upper(&self) -> &T {
        match self.dir {
            RangeDir::To => &self.right,
            RangeDir::Downto => &self.left,
        }
    }

    /// Return true if the range is a null range.
    ///
    /// A null range has its lower bound greater than or equal to its upper
    /// bound, and thus also a length of 0 or lower.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::IntegerRange;
    ///
    /// let a = IntegerRange::ascending(0, 42);
    /// let b = IntegerRange::ascending(42, 0);
    ///
    /// assert_eq!(a.is_null(), false);
    /// assert_eq!(b.is_null(), true);
    /// ```
    pub fn is_null(&self) -> bool {
        self.lower() >= self.upper()
    }

    /// Return the length of the range.
    ///
    /// The length of a range is defined as `upper + 1 - lower`. The result may
    /// be negative, indicating that the range is a null range.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{IntegerRange, BigInt};
    ///
    /// let a = IntegerRange::ascending(0, 42);
    /// let b = IntegerRange::ascending(42, 0);
    ///
    /// assert_eq!(a.len(), BigInt::from(43));
    /// assert_eq!(b.len(), BigInt::from(-41));
    /// ```
    pub fn len(&self) -> T {
        &(self.upper() + &One::one()) - self.lower()
    }
}

impl<T: Display> Display for Range<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} {}", self.left, self.dir, self.right)
    }
}

/// A range of integer values.
pub type IntegerRange = Range<BigInt>;

/// A range of real values.
pub type RealRange = Range<BigRational>;

/// A range direction.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RangeDir {
    /// An ascending range.
    To,
    /// A descending range.
    Downto,
}

impl Display for RangeDir {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RangeDir::To => write!(f, "to"),
            RangeDir::Downto => write!(f, "downto"),
        }
    }
}

/// A null type.
///
/// This type is not strictly part of the VHDL type system. Rather, arrays that
/// have negative length degenerate into null arrays. We handle these types
/// explicitly, since they significantly change how types match.
pub struct NullType;
