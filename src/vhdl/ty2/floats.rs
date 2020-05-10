// Copyright (c) 2016-2020 Fabian Schuiki

//! Floating-point types.

use std::fmt::{self, Display};
use std::ops::Deref;

use crate::ty2::prelude::*;
use crate::ty2::ScalarSubtype;

/// A real type.
///
/// This can either be an `FloatingBasetype` or an `FloatingSubtype`.
pub trait FloatingType: Type {
    /// Convert to a type.
    fn as_type(&self) -> &Type;

    /// The range of values this real can assume.
    ///
    /// Universal integers return `None` here, as they do not have a value range
    /// associated with them.
    fn range(&self) -> Option<&Range<f64>>;

    /// The base type of this real.
    fn base_type(&self) -> &Type;

    /// The resolution function associated with this type.
    fn resolution_func(&self) -> Option<usize> {
        None
    }

    /// Returns `Some` if self is an `FloatingBasetype`, `None` otherwise.
    fn as_basetype(&self) -> Option<&FloatingBasetype> {
        None
    }

    /// Returns `Some` if self is an `FloatingSubtype`, `None` otherwise.
    fn as_subtype(&self) -> Option<&FloatingSubtype> {
        None
    }

    /// Checks whether this is a universal real type.
    fn is_universal(&self) -> bool {
        false
    }

    /// Returns an `&FloatingBasetype` or panics if the type is not a basetype.
    fn unwrap_basetype(&self) -> &FloatingBasetype {
        self.as_basetype().expect("real type is not a basetype")
    }

    /// Returns an `&FloatingSubtype` or panics if the type is not a subtype.
    fn unwrap_subtype(&self) -> &FloatingSubtype {
        self.as_subtype().expect("real type is not a subtype")
    }

    /// Check if two real types are equal.
    fn is_equal(&self, other: &FloatingType) -> bool;
}

impl<'t> PartialEq for FloatingType + 't {
    fn eq(&self, other: &FloatingType) -> bool {
        FloatingType::is_equal(self, other)
    }
}

impl<'t> Eq for FloatingType + 't {}

macro_rules! common_type_impl {
    () => {
        fn is_scalar(&self) -> bool {
            true
        }

        fn is_discrete(&self) -> bool {
            false
        }

        fn is_numeric(&self) -> bool {
            true
        }

        fn is_composite(&self) -> bool {
            false
        }

        fn as_any(&self) -> AnyType {
            AnyType::Floating(self)
        }
    };
}

/// A real base type.
#[derive(Debug, Clone, PartialEq)]
pub struct FloatingBasetype {
    /// The range of values.
    range: Range<f64>,
}

impl Eq for FloatingBasetype {}

impl FloatingBasetype {
    /// Create a new real type.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate moore_vhdl;
    /// # extern crate num;
    /// # fn main() {
    /// use moore_vhdl::ty2::{Type, FloatingBasetype, Range, RangeDir};
    ///
    /// let a = FloatingBasetype::new(Range::ascending(0, 42));
    /// let b = FloatingBasetype::new(Range::descending(42, 0));
    ///
    /// assert_eq!(format!("{}", a), "0 to 42");
    /// assert_eq!(format!("{}", b), "42 downto 0");
    /// assert_eq!(a.dir(), RangeDir::To);
    /// assert_eq!(b.dir(), RangeDir::Downto);
    /// assert_eq!(a.len(), 43 as f64);
    /// assert_eq!(b.len(), 43 as f64);
    /// # }
    /// ```
    pub fn new(range: Range<f64>) -> FloatingBasetype {
        FloatingBasetype { range: range }
    }
}

impl Type for FloatingBasetype {
    common_type_impl!();

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::FloatingBasetype(self)
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::FloatingBasetype(self.clone())
    }
}

impl FloatingType for FloatingBasetype {
    fn as_type(&self) -> &Type {
        self
    }

    fn range(&self) -> Option<&Range<f64>> {
        Some(&self.range)
    }

    fn base_type(&self) -> &Type {
        self
    }

    fn as_basetype(&self) -> Option<&FloatingBasetype> {
        Some(self)
    }

    fn is_equal(&self, other: &FloatingType) -> bool {
        other.as_basetype().map(|t| self == t).unwrap_or(false)
    }
}

impl Deref for FloatingBasetype {
    type Target = Range<f64>;
    fn deref(&self) -> &Range<f64> {
        &self.range
    }
}

impl Display for FloatingBasetype {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.range)
    }
}

/// A subtype of an real type.
pub type FloatingSubtype<'t> = ScalarSubtype<'t, FloatingType, f64>;

impl<'t> FloatingSubtype<'t> {
    /// Create a new real subtype.
    ///
    /// Returns `Some(...)` if `range` is a subrange of the real, or `None`
    /// otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_common::name::get_name_table;
    /// use moore_vhdl::ty2::{Type, TypeMark, FloatingBasetype, FloatingSubtype, Range};
    ///
    /// let ty = FloatingBasetype::new(Range::ascending(0.0, 1.0));
    /// let tm = TypeMark::new(
    ///     get_name_table().intern("UNIT", false),
    ///     &ty,
    /// );
    /// let a = FloatingSubtype::new(&tm, Range::ascending(0.0, 0.5)).unwrap();
    /// let b = FloatingSubtype::new(&tm, Range::descending(0.5, 0.0)).unwrap();
    ///
    /// assert_eq!(format!("{}", a), "UNIT range 0 to 0.5");
    /// assert_eq!(format!("{}", b), "UNIT range 0.5 downto 0");
    /// ```
    pub fn new(mark: &'t TypeMark<'t>, range: Range<f64>) -> Option<FloatingSubtype<'t>> {
        let base = mark.as_any().unwrap_floating();
        let base_range = base.range()?;
        if base_range.has_subrange(&range) {
            Some(FloatingSubtype {
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

impl<'t> Type for FloatingSubtype<'t> {
    common_type_impl!();

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::FloatingSubtype(self)
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::FloatingSubtype(self.clone())
    }
}

impl<'t> FloatingType for FloatingSubtype<'t> {
    fn as_type(&self) -> &Type {
        self
    }

    fn range(&self) -> Option<&Range<f64>> {
        Some(&self.con)
    }

    fn base_type(&self) -> &Type {
        self.base.as_type()
    }

    fn as_subtype(&self) -> Option<&FloatingSubtype> {
        Some(self)
    }

    fn is_equal(&self, other: &FloatingType) -> bool {
        other.as_subtype().map(|t| self == t).unwrap_or(false)
    }
}

impl<'t> Display for FloatingSubtype<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} range {}", self.mark, self.con)
    }
}

/// A universal real.
///
/// This is not strictly a separate type, but rather defined by the standard as
/// the real type with the largest range. However since we can represent
/// arbitrary numbers as `f64`, we use this special marker type.
///
/// # Example
///
/// ```
/// use moore_vhdl::ty2::{Type, UniversalRealType};
///
/// let ty = UniversalRealType;
///
/// assert_eq!(format!("{}", ty), "{universal real}");
/// assert_eq!(ty.is_scalar(), true);
/// assert_eq!(ty.is_discrete(), false);
/// assert_eq!(ty.is_numeric(), true);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct UniversalRealType;

impl Type for UniversalRealType {
    common_type_impl!();

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::UniversalReal
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::UniversalReal
    }
}

impl FloatingType for UniversalRealType {
    fn as_type(&self) -> &Type {
        self
    }

    fn range(&self) -> Option<&Range<f64>> {
        None
    }

    fn base_type(&self) -> &Type {
        self
    }

    fn is_universal(&self) -> bool {
        true
    }

    fn is_equal(&self, other: &FloatingType) -> bool {
        other.is_universal()
    }
}

impl Display for UniversalRealType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{universal real}}")
    }
}
