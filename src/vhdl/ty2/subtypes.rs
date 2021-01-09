// Copyright (c) 2016-2021 Fabian Schuiki

//! The subtyping mechanism.

use std::fmt::{Debug, Display};

pub use num::BigInt;

use crate::ty2::marks::*;
use crate::ty2::range::*;
use crate::ty2::types::*;

/// An interface for dealing with subtypes.
pub trait Subtype: Debug + Display {}

/// A subtype of a scalar type.
///
/// Scalar types may be subtyped by a range constraint.
#[derive(Debug, PartialEq)]
pub struct ScalarSubtype<'t, T: Type + ?Sized + 't, C: Clone> {
    #[allow(dead_code)]
    pub(crate) resfn: Option<usize>,
    pub(crate) mark: &'t TypeMark<'t>,
    pub(crate) base: &'t T,
    pub(crate) con: Range<C>,
}

impl<'t, T: Type + ?Sized + 't + PartialEq, C: Clone + PartialEq> Eq for ScalarSubtype<'t, T, C> {}

impl<'t, T: Type + ?Sized + 't, C: Clone> Clone for ScalarSubtype<'t, T, C> {
    fn clone(&self) -> Self {
        ScalarSubtype {
            resfn: self.resfn.clone(),
            mark: self.mark,
            base: self.base,
            con: self.con.clone(),
        }
    }
}
