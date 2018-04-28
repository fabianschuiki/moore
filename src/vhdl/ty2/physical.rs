// Copyright (c) 2018 Fabian Schuiki

//! Physical types.

use std::fmt::{self, Display};
use std::ops::Deref;
use std::iter::{once, repeat};

pub use num::BigInt;

use common::name::Name;
use ty2::prelude::*;
use ty2::ScalarSubtype;

/// A physical type.
///
/// This can either be an `PhysicalBasetype` or a `PhysicalSubtype`.
pub trait PhysicalType: Type {
    /// Convert to a type.
    fn as_type(&self) -> &Type;

    /// The range of values this physical type can assume.
    fn range(&self) -> &Range<BigInt>;

    /// The units of measure of this type.
    fn units(&self) -> &[PhysicalUnit];

    /// The index of the primary unit.
    fn primary_index(&self) -> usize;

    /// The base type of this physical type.
    fn base_type(&self) -> &Type;

    /// The resolution function associated with this type.
    fn resolution_func(&self) -> Option<usize> {
        None
    }

    /// Returns `Some` if self is a `PhysicalBasetype`, `None` otherwise.
    fn as_basetype(&self) -> Option<&PhysicalBasetype> {
        None
    }

    /// Returns `Some` if self is a `PhysicalSubtype`, `None` otherwise.
    fn as_subtype(&self) -> Option<&PhysicalSubtype> {
        None
    }

    /// Returns an `&PhysicalBasetype` or panics if the type is not a basetype.
    fn unwrap_basetype(&self) -> &PhysicalBasetype {
        self.as_basetype().expect("physical type is not a basetype")
    }

    /// Returns an `&PhysicalSubtype` or panics if the type is not a subtype.
    fn unwrap_subtype(&self) -> &PhysicalSubtype {
        self.as_subtype().expect("physical type is not a subtype")
    }

    /// Check if two physical types are equal.
    fn is_equal(&self, other: &PhysicalType) -> bool;
}

impl<'t> PartialEq for PhysicalType + 't {
    fn eq(&self, other: &PhysicalType) -> bool {
        PhysicalType::is_equal(self, other)
    }
}

impl<'t> Eq for PhysicalType + 't {}

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
            AnyType::Physical(self)
        }
    }
}

/// A physical base type.
///
/// In VHDL a physical type is an integer multiple of some measurement unit.
/// A physical type has exactly one primary unit, and multiple secondary units
/// defined as multiples of that primary unit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhysicalBasetype {
    /// The range of integer multiples of the primary unit.
    range: Range<BigInt>,
    /// The units of this type.
    units: Vec<PhysicalUnit>,
    /// The index of the primary unit.
    primary: usize,
}

impl PhysicalBasetype {
    /// Create a new physical type.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{PhysicalBasetype, PhysicalUnit, Range};
    /// use moore_vhdl::common::name::get_name_table;
    ///
    /// let ty = PhysicalBasetype::new(Range::ascending(0, 1_000_000), vec![
    ///     PhysicalUnit::primary(get_name_table().intern("fs", false), 1),
    ///     PhysicalUnit::secondary(get_name_table().intern("ps", false), 1_000, 1000, 0),
    ///     PhysicalUnit::secondary(get_name_table().intern("ns", false), 1_000_000, 1000, 1),
    /// ], 0);
    ///
    /// assert_eq!(format!("{}", ty), "0 to 1000000 units (fs, ps, ns)");
    /// ```
    pub fn new<I>(range: Range<BigInt>, units: I, primary: usize) -> PhysicalBasetype
    where
        I: IntoIterator<Item = PhysicalUnit>,
    {
        PhysicalBasetype {
            range: range,
            units: units.into_iter().collect(),
            primary: primary,
        }
    }
}

impl Type for PhysicalBasetype {
    common_type_impl!();

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::PhysicalBasetype(self)
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::PhysicalBasetype(self.clone())
    }
}

impl PhysicalType for PhysicalBasetype {
    fn as_type(&self) -> &Type {
        self
    }

    fn range(&self) -> &Range<BigInt> {
        &self.range
    }

    fn units(&self) -> &[PhysicalUnit] {
        &self.units
    }

    fn primary_index(&self) -> usize {
        self.primary
    }

    fn base_type(&self) -> &Type {
        self
    }

    fn as_basetype(&self) -> Option<&PhysicalBasetype> {
        Some(self)
    }

    fn is_equal(&self, other: &PhysicalType) -> bool {
        other.as_basetype().map(|t| self == t).unwrap_or(false)
    }
}

impl Display for PhysicalBasetype {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} units (", self.range)?;
        for (sep, unit) in once("").chain(repeat(", ")).zip(self.units.iter()) {
            write!(f, "{}{}", sep, unit.name)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl Deref for PhysicalBasetype {
    type Target = Range<BigInt>;
    fn deref(&self) -> &Range<BigInt> {
        &self.range
    }
}

/// A subtype of an integer type.
pub type PhysicalSubtype<'t> = ScalarSubtype<'t, PhysicalType, BigInt>;

impl<'t> PhysicalSubtype<'t> {
    /// Create a new integer subtype.
    ///
    /// Returns `Some(...)` if `range` is a subrange of the integer, or `None`
    /// otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{Type, TypeMark, PhysicalBasetype, PhysicalSubtype, Range};
    /// use moore_vhdl::common::name::get_name_table;
    ///
    /// let ty = PhysicalBasetype::new(Range::ascending(-1000isize, 1000isize), vec![
    ///     PhysicalUnit::primary(get_name_table().intern("fs", false), 1),
    ///     PhysicalUnit::secondary(get_name_table().intern("ps", false), 1000, 1000, 0),
    /// ], 0);
    /// let tm = TypeMark::new(
    ///     get_name_table().intern("TIME", false),
    ///     &ty,
    /// );
    /// let a = PhysicalSubtype::new(&tm, Range::ascending(0isize, 100isize)).unwrap();
    /// let b = PhysicalSubtype::new(&tm, Range::descending(100isize, 0isize)).unwrap();
    ///
    /// assert_eq!(format!("{}", a), "TIME range 0 to 100");
    /// assert_eq!(format!("{}", b), "TIME range 100 downto 0");
    /// ```
    pub fn new(mark: &'t TypeMark<'t>, range: Range<BigInt>) -> Option<PhysicalSubtype<'t>> {
        let base = mark.as_any().as_physical()?;
        let base_range = base.range();
        if base_range.has_subrange(&range) {
            Some(PhysicalSubtype {
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

impl<'t> Type for PhysicalSubtype<'t> {
    common_type_impl!();

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::PhysicalSubtype(self)
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::PhysicalSubtype(self.clone())
    }
}

impl<'t> PhysicalType for PhysicalSubtype<'t> {
    fn as_type(&self) -> &Type {
        self
    }

    fn range(&self) -> &Range<BigInt> {
        &self.con
    }

    fn units(&self) -> &[PhysicalUnit] {
        self.base.units()
    }

    fn primary_index(&self) -> usize {
        self.base.primary_index()
    }

    fn base_type(&self) -> &Type {
        self.base.as_type()
    }

    fn as_subtype(&self) -> Option<&PhysicalSubtype> {
        Some(self)
    }

    fn is_equal(&self, other: &PhysicalType) -> bool {
        other.as_subtype().map(|t| self == t).unwrap_or(false)
    }
}

impl<'t> Display for PhysicalSubtype<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} range {}", self.mark, self.con)
    }
}

/// A unit of a physical type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhysicalUnit {
    /// The name of the unit.
    pub name: Name,
    /// The scale of the unit with respect to the physical type's primary unit.
    pub abs: BigInt,
    /// The scale of the unit with respect to another unit.
    pub rel: Option<(BigInt, usize)>,
}

impl PhysicalUnit {
    /// Create a new unit.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{PhysicalUnit, BigInt};
    /// use moore_vhdl::common::name::get_name_table;
    ///
    /// let name = get_name_table().intern("fs", false);
    /// let unit = PhysicalUnit::new(name, 1, Some((1000, 0)));
    ///
    /// assert_eq!(unit.name, name);
    /// assert_eq!(unit.abs, BigInt::from(1));
    /// assert_eq!(unit.rel, Some((BigInt::from(1000), 0)));
    /// ```
    pub fn new<A, R>(name: Name, abs: A, rel: Option<(R, usize)>) -> PhysicalUnit
    where
        BigInt: From<A> + From<R>,
    {
        PhysicalUnit {
            name: name,
            abs: abs.into(),
            rel: rel.map(|(rel, rel_to)| (rel.into(), rel_to)),
        }
    }

    /// Create a new primary unit.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{PhysicalUnit, BigInt};
    /// use moore_vhdl::common::name::get_name_table;
    ///
    /// let name = get_name_table().intern("fs", false);
    /// let unit = PhysicalUnit::primary(name, 1);
    ///
    /// assert_eq!(unit.name, name);
    /// assert_eq!(unit.abs, BigInt::from(1));
    /// assert_eq!(unit.rel, None);
    /// ```
    pub fn primary<A>(name: Name, abs: A) -> PhysicalUnit
    where
        BigInt: From<A>,
    {
        PhysicalUnit {
            name: name,
            abs: abs.into(),
            rel: None,
        }
    }

    /// Create a new secondary unit.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{PhysicalUnit, BigInt};
    /// use moore_vhdl::common::name::get_name_table;
    ///
    /// let name = get_name_table().intern("fs", false);
    /// let unit = PhysicalUnit::secondary(name, 1, 1000, 0);
    ///
    /// assert_eq!(unit.name, name);
    /// assert_eq!(unit.abs, BigInt::from(1));
    /// assert_eq!(unit.rel, Some((BigInt::from(1000), 0)));
    /// ```
    pub fn secondary<A, R>(name: Name, abs: A, rel: R, rel_to: usize) -> PhysicalUnit
    where
        BigInt: From<A> + From<R>,
    {
        PhysicalUnit {
            name: name,
            abs: abs.into(),
            rel: Some((rel.into(), rel_to)),
        }
    }
}
