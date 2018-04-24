// Copyright (c) 2017-2018 Fabian Schuiki

//! The subtyping mechanism.

use std::fmt::{Debug, Display};

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
    pub(crate) resfn: Option<usize>,
    pub(crate) mark: &'t TypeMark<'t>,
    pub(crate) base: &'t T,
    pub(crate) con: Range<C>,
}

/// A subtype of a floating-point type.
pub type FloatingSubtype<'t> = ScalarSubtype<'t, FloatingType, f64>;

/// A subtype of a physical type.
pub type PhysicalSubtype<'t> = ScalarSubtype<'t, PhysicalType, BigInt>;
