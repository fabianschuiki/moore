// Copyright (c) 2018 Fabian Schuiki

use std::borrow::Cow;
use std::fmt;

use crate::konst2::traits::*;
use crate::ty2::{FloatingType, Type};

/// A constant float value.
#[derive(Debug, Clone, PartialEq)]
pub struct FloatingConst<'t> {
    ty: &'t FloatingType,
    value: f64,
}

impl<'t> FloatingConst<'t> {
    /// Create a new constant float.
    ///
    /// Returns an `OutOfRange` error if the value is outside the type's range.
    pub fn try_new(ty: &'t FloatingType, value: f64) -> Result<FloatingConst<'t>, ConstError> {
        let valid = match ty.range() {
            Some(r) => r.contains(&value),
            None => true,
        };
        if valid {
            Ok(FloatingConst {
                ty: ty,
                value: value,
            })
        } else {
            Err(ConstError::OutOfRange)
        }
    }

    /// Return the float type.
    pub fn floating_type(&self) -> &'t FloatingType {
        self.ty
    }

    /// Return the float value.
    pub fn value(&self) -> f64 {
        self.value
    }
}

impl<'t> Const2<'t> for FloatingConst<'t> {
    fn ty(&self) -> &'t Type {
        self.ty.as_type()
    }

    fn as_any<'a>(&'a self) -> AnyConst<'a, 't> {
        AnyConst::Floating(self)
    }

    fn into_owned(self) -> OwnedConst<'t> {
        OwnedConst::Floating(self)
    }

    fn to_owned(&self) -> OwnedConst<'t> {
        OwnedConst::Floating(self.clone())
    }

    fn cast(&self, ty: &'t Type) -> Result<Cow<Const2<'t> + 't>, ConstError> {
        if self.ty.as_type() == ty {
            return Ok(Cow::Borrowed(self));
        }
        unimplemented!("casting of float constants")
    }
}

impl<'t> fmt::Display for FloatingConst<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

// We have to explicitly implement this, since f64 by default does not, causing
// the usual derive(Eq) to fail.
impl<'t> Eq for FloatingConst<'t> {}
