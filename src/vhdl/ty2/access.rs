// Copyright (c) 2018 Fabian Schuiki

//! Access types.

use std::fmt::{self, Display};

use crate::ty2::prelude::*;

/// An access type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccessType<'t> {
    /// The type of value being pointed to.
    inner: &'t Type,
}

impl<'t> AccessType<'t> {
    /// Create a new access type.
    ///
    /// # Example
    ///
    /// ```
    /// use moore_vhdl::ty2::{Type, AccessType, IntegerBasetype, Range};
    ///
    /// let a = IntegerBasetype::new(Range::ascending(0, 42));
    /// let ty = AccessType::new(&a);
    ///
    /// assert_eq!(format!("{}", ty), "access 0 to 42");
    /// ```
    pub fn new(inner: &'t Type) -> AccessType<'t> {
        AccessType { inner: inner }
    }
}

impl<'t> Type for AccessType<'t> {
    fn is_scalar(&self) -> bool {
        false
    }

    fn is_discrete(&self) -> bool {
        false
    }

    fn is_numeric(&self) -> bool {
        false
    }

    fn is_composite(&self) -> bool {
        false
    }

    fn into_owned<'a>(self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::Access(self)
    }

    fn to_owned<'a>(&self) -> OwnedType<'a>
    where
        Self: 'a,
    {
        OwnedType::Access(self.clone())
    }

    fn as_any(&self) -> AnyType {
        AnyType::Access(self)
    }
}

impl<'t> Display for AccessType<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "access {}", self.inner)
    }
}
