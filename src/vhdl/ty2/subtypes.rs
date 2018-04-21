// Copyright (c) 2017-2018 Fabian Schuiki

//! The subtyping mechanism.

use std::fmt::{self, Debug, Display};

pub use num::BigInt;

use ty2::types::*;
use ty2::marks::*;
use ty2::range::*;

/// An interface for dealing with subtypes.
pub trait Subtype: Debug + Display {}

/// A subtype of a scalar type.
///
/// Scalar types may be subtyped by a range constraint.
#[derive(Debug, PartialEq, Eq)]
pub struct ScalarSubtype<'t, T: Type + ?Sized + 't, C> {
    #[allow(dead_code)]
    resfn: Option<usize>,
    mark: &'t TypeMark<'t>,
    base: &'t T,
    con: Range<C>,
}

/// A subtype of an enumeration type.
pub type EnumSubtype<'t> = ScalarSubtype<'t, EnumType, usize>;

impl<'t> EnumSubtype<'t> {
    /// Create a new enumeration subtype.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{Type, TypeMark, EnumType, EnumSubtype, Range};
    /// use moore_vhdl::common::name::get_name_table;
    ///
    /// let ty = EnumType::new(vec![
    ///     "first".into(),
    ///     "second".into(),
    ///     '0'.into(),
    ///     '1'.into(),
    /// ]);
    /// let tm = TypeMark::new(
    ///     get_name_table().intern("MY_TYPE", false),
    ///     &ty,
    /// );
    /// let subty = EnumSubtype::new(&tm, Range::ascending(1usize, 2usize));
    ///
    /// assert_eq!(format!("{}", subty), "MY_TYPE range second to '0'");
    /// ```
    pub fn new(mark: &'t TypeMark, con: Range<usize>) -> EnumSubtype<'t> {
        let base = mark.as_any().unwrap_enum();
        assert!(*con.upper() <= base.len());
        EnumSubtype {
            resfn: None,
            mark: mark,
            base: base,
            con: con,
        }
    }
}

impl<'t> Subtype for EnumSubtype<'t> {}

impl<'t> Display for EnumSubtype<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} range {} {} {}",
            self.mark,
            self.base.literal(*self.con.left()),
            self.con.dir(),
            self.base.literal(*self.con.right()),
        )
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
    /// use moore_vhdl::ty2::{Type, TypeMark, IntegerType, IntegerSubtype, Range};
    /// use moore_vhdl::common::name::get_name_table;
    ///
    /// let ty = IntegerType::new(Range::ascending(0usize, 255usize));
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
        let base_range = base.range();
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
    fn range(&self) -> &Range<BigInt> {
        &self.con
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

/// A subtype of a floating-point type.
pub type FloatingSubtype<'t> = ScalarSubtype<'t, FloatingType, f64>;

/// A subtype of a physical type.
pub type PhysicalSubtype<'t> = ScalarSubtype<'t, PhysicalType, BigInt>;
