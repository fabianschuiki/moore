// Copyright (c) 2017-2018 Fabian Schuiki

//! The fundamental base types.

use std::fmt::{self, Display};
use std::ops::Deref;

pub use num::BigInt;

use ty2::types::*;
use ty2::range::*;

/// An integer base type.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct IntegerBasetype {
    /// The range of values.
    range: Range<BigInt>,
}

impl IntegerType {
    /// Create a new integer type.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate moore_vhdl;
    /// # extern crate num;
    /// # fn main() {
    /// use moore_vhdl::ty2::{Type, IntegerType, Range, RangeDir};
    /// use num::BigInt;
    ///
    /// let a = IntegerType::new(Range::ascending(0, 42));
    /// let b = IntegerType::new(Range::descending(42, 0));
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

    fn range(&self) -> &Range<BigInt> {
        &self.range
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
        self.range()
    }
}

impl Display for IntegerBasetype {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.range)
    }
}
