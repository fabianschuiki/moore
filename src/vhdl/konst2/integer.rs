// Copyright (c) 2018 Fabian Schuiki

use std::fmt;
use std::borrow::Cow;

use num::BigInt;

use konst2::traits::*;
use ty2::{IntegerType, Type};

/// A constant integer value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerConst<'t> {
    ty: &'t IntegerType,
    value: BigInt,
}

impl<'t> IntegerConst<'t> {
    /// Create a new constant integer.
    ///
    /// Returns an `OutOfRange` error if the value is outside the type's range.
    pub fn try_new(ty: &'t IntegerType, value: BigInt) -> Result<IntegerConst<'t>, ConstError> {
        let valid = match ty.range() {
            Some(r) => r.contains(&value),
            None => true,
        };
        if valid {
            Ok(IntegerConst {
                ty: ty,
                value: value,
            })
        } else {
            Err(ConstError::OutOfRange)
        }
    }

    /// Return the integer type.
    pub fn integer_type(&self) -> &'t IntegerType {
        self.ty
    }

    /// Return the integer value.
    pub fn value(&self) -> &BigInt {
        &self.value
    }
}

impl<'t> Const2<'t> for IntegerConst<'t> {
    fn ty(&self) -> &'t Type {
        self.ty.as_type()
    }

    fn as_any(&self) -> AnyConst {
        AnyConst::Integer(self)
    }

    fn to_owned(&self) -> OwnedConst<'t> {
        OwnedConst::Integer(self.clone())
    }

    fn cast(&self, ty: &'t Type) -> Result<Cow<Const2<'t>>, ConstError> {
        if self.ty.as_type() == ty {
            return Ok(Cow::Borrowed(self));
        }
        unimplemented!("casting of integer constants")
    }
}

impl<'t> fmt::Display for IntegerConst<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
