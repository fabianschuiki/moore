// Copyright (c) 2017 Fabian Schuiki

use std::fmt::{self, Debug, Display};
use std::borrow::{Borrow, Cow};

use common::errors::*;

use ty2::Type;
use konst2::integer::IntegerConst;

/// An interface for dealing with constants.
///
/// This is the main trait which all constant values implement. Its purpose is
/// to provide a convenient interface for inspecting and manipulating values.
/// Dedicated structs for the specific types (e.g. integers, arrays, etc.) are
/// expected to be allocated/internalized into an arena for ease of use.
pub trait Const2<'t>: Debug + Display {
    /// Return the type of the constant.
    fn ty(&self) -> &'t Type;

    /// Clone this constant.
    fn to_owned(&self) -> OwnedConst<'t>;

    /// Converts from `&Const2` to `AnyConst`.
    fn as_any<'r>(&'r self) -> AnyConst<'r, 't>;

    /// Cast the constant to a different type.
    fn cast(&self, ty: &'t Type) -> Result<Cow<Const2<'t> + 't>, ConstError>;
}

impl<'t> ToOwned for Const2<'t> + 't {
    type Owned = OwnedConst<'t>;

    fn to_owned(&self) -> OwnedConst<'t> {
        Const2::to_owned(self)
    }
}

/// An error resulting from a function call on a constant.
#[derive(Debug, Clone)]
pub enum ConstError {
    /// The given value lies outside the range of the value's type.
    OutOfRange,
}

impl EmitError for ConstError {
    type Output = ();

    fn emit<C: DiagEmitter>(self, ctx: C) {
        match self {
            ConstError::OutOfRange => ctx.emit(DiagBuilder2::error("constant value out of range")),
        }
    }
}

/// A borrowed constant.
#[derive(Copy, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum AnyConst<'r, 't: 'r> {
    Integer(&'r IntegerConst<'t>),
}

impl<'r, 't: 't> Const2<'t> for AnyConst<'r, 't> {
    fn ty(&self) -> &'t Type {
        match *self {
            AnyConst::Integer(t) => t.ty(),
        }
    }

    fn to_owned(&self) -> OwnedConst<'t> {
        match *self {
            AnyConst::Integer(t) => Const2::to_owned(t),
        }
    }

    fn as_any<'a>(&'a self) -> AnyConst<'a, 't> {
        *self
    }

    fn cast(&self, ty: &'t Type) -> Result<Cow<Const2<'t> + 't>, ConstError> {
        match *self {
            AnyConst::Integer(t) => t.cast(ty),
        }
    }
}

impl<'r, 't> Display for AnyConst<'r, 't> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnyConst::Integer(t) => Display::fmt(t, f),
        }
    }
}

impl<'r, 't> Debug for AnyConst<'r, 't> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnyConst::Integer(t) => Debug::fmt(t, f),
        }
    }
}

impl<'r, 't, T: Const2<'t>> From<&'r T> for AnyConst<'r, 't> {
    fn from(konst: &'r T) -> AnyConst<'r, 't> {
        konst.as_any()
    }
}

#[allow(unreachable_patterns)]
impl<'r, 't> AnyConst<'r, 't> {
    /// Perform type erasure.
    pub fn as_const(self) -> &'r Const2<'t> {
        match self {
            AnyConst::Integer(k) => k,
        }
    }

    /// Returns `Some(k)` if the constant is `Integer(k)`, `None` otherwise.
    pub fn as_integer(self) -> Option<&'r IntegerConst<'t>> {
        match self {
            AnyConst::Integer(k) => Some(k),
            _ => None,
        }
    }

    /// Returns an `&IntegerConst` or panics if the constant is not `Integer`.
    pub fn unwrap_integer(self) -> &'r IntegerConst<'t> {
        self.as_integer().expect("constant is not an integer")
    }
}

/// An owned constant.
#[derive(Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum OwnedConst<'t> {
    Integer(IntegerConst<'t>),
}

impl<'t> Borrow<Const2<'t> + 't> for OwnedConst<'t> {
    fn borrow(&self) -> &(Const2<'t> + 't) {
        match *self {
            OwnedConst::Integer(ref k) => k,
        }
    }
}

impl<'t> Display for OwnedConst<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            OwnedConst::Integer(ref t) => Display::fmt(t, f),
        }
    }
}

impl<'t> Debug for OwnedConst<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            OwnedConst::Integer(ref t) => Debug::fmt(t, f),
        }
    }
}

impl<'t, T: Const2<'t>> From<T> for OwnedConst<'t> {
    fn from(konst: T) -> OwnedConst<'t> {
        konst.to_owned()
    }
}
