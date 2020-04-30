// Copyright (c) 2016-2020 Fabian Schuiki

//! Dealing with types in an abstract manner.

use std::fmt::{self, Display};
use std::ops::{Add, Sub};

pub use num::BigInt;
use num::One;

/// A directed range of values.
///
/// `Range<T>` has the same semantics as ranges in VHDL. They have a direction
/// associated with them, and left and right bounds. The range may be a null
/// range if the lower bound is greater than or equal to the upper bound.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Range<T> {
    /// The direction.
    dir: RangeDir,
    /// The left bound.
    left: T,
    /// The right bound.
    right: T,
}

impl<T: PartialOrd + One> Range<T>
where
    for<'a> &'a T: Add<Output = T> + Sub<Output = T>,
{
    /// Create a range from left and right bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{IntegerRange, RangeDir};
    ///
    /// let a = IntegerRange::with_left_right(RangeDir::To, 0, 42);
    /// let b = IntegerRange::with_left_right(RangeDir::Downto, 42, 0);
    ///
    /// assert_eq!(format!("{}", a), "0 to 42");
    /// assert_eq!(format!("{}", b), "42 downto 0");
    /// ```
    pub fn with_left_right<D, L, R>(dir: D, left: L, right: R) -> Range<T>
    where
        RangeDir: From<D>,
        T: From<L> + From<R>,
    {
        Range {
            dir: dir.into(),
            left: left.into(),
            right: right.into(),
        }
    }

    /// Create a range from lower and upper bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{IntegerRange, RangeDir};
    ///
    /// let a = IntegerRange::with_lower_upper(RangeDir::To, 0, 42);
    /// let b = IntegerRange::with_lower_upper(RangeDir::Downto, 0, 42);
    ///
    /// assert_eq!(format!("{}", a), "0 to 42");
    /// assert_eq!(format!("{}", b), "42 downto 0");
    /// ```
    pub fn with_lower_upper<D, L, U>(dir: D, lower: L, upper: U) -> Range<T>
    where
        RangeDir: From<D>,
        T: From<L> + From<U>,
    {
        let dir = dir.into();
        let (left, right) = match dir {
            RangeDir::To => (lower.into(), upper.into()),
            RangeDir::Downto => (upper.into(), lower.into()),
        };
        Range {
            dir: dir,
            left: left,
            right: right,
        }
    }

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
    pub fn ascending<L, R>(left: L, right: R) -> Range<T>
    where
        T: From<L> + From<R>,
    {
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
    pub fn descending<L, R>(left: L, right: R) -> Range<T>
    where
        T: From<L> + From<R>,
    {
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

    /// Check if another range is a subrange of this range.
    ///
    /// This function checks if `self.lower()` is less than or equal to, and
    /// `self.upper()` is larger than or equal to, the corresponding bounds of
    /// the subrange.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{IntegerRange, BigInt};
    ///
    /// let a = IntegerRange::ascending(0, 42);
    /// let b = IntegerRange::ascending(4, 16);
    /// let c = IntegerRange::descending(16, 4);
    ///
    /// assert_eq!(a.has_subrange(&b), true);
    /// assert_eq!(a.has_subrange(&c), true);
    /// assert_eq!(b.has_subrange(&a), false);
    /// assert_eq!(c.has_subrange(&a), false);
    /// assert_eq!(b.has_subrange(&c), true);
    /// assert_eq!(c.has_subrange(&b), true);
    /// ```
    pub fn has_subrange(&self, subrange: &Self) -> bool {
        self.lower() <= subrange.lower() && self.upper() >= subrange.upper()
    }

    /// Check if a value is within this range.
    ///
    /// This function checks if `self.lower()` is less than or equal to, and
    /// `self.upper()` is larger than or equal to, the given value.
    pub fn contains(&self, value: &T) -> bool {
        self.lower() <= value && self.upper() >= value
    }
}

impl<T: Display> Display for Range<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} {}", self.left, self.dir, self.right)
    }
}

// Implement `Clone` for ranges whose type implements it.
impl<T: Clone> Clone for Range<T> {
    fn clone(&self) -> Range<T> {
        Range {
            dir: self.dir.clone(),
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }
}

// Implement `Copt` for ranges whose type implements it.
impl<T: Copy> Copy for Range<T> {}

/// A range of integer values.
pub type IntegerRange = Range<BigInt>;

/// A range of real values.
pub type RealRange = Range<f64>;

/// A range direction.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
