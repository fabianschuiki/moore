// Copyright (c) 2017 Fabian Schuiki

//! This module implements VHDL types.

use std::fmt;
use score::*;
use moore_common::source::Span;
use num::BigInt;
pub use hir::Dir;


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
	/// A named type. In a signal declaration for example, the source code
	/// mentions the type of the signal. This type name is resolved to its
	/// actual declaration somewhere else in the source code. Thus this type
	/// acts as a sort of "pointer" to a type, together with information on how
	/// the source code referred to that type. This helps make error messages
	/// easier to read for the user.
	Named(Span, TypeMarkRef),
	/// The null type.
	Null,
	/// An integer type.
	Int(IntTy),
	/// An unbounded integer type. This is the type integers have that are
	/// evaluated at compile time, e.g. as part of a range expression. Cannot be
	/// mapped to LLHD.
	UnboundedInt,
	/// An enumeration type.
	Enum(EnumTy),
	/// An access type.
	Access(Box<Ty>),
}

impl Ty {
	/// Provide a textual description of the kind of type. For example, if
	/// called on an integer type, the result is `"integer type"`, without any
	/// information on the exact nature of the integer.
	pub fn kind_desc(&self) -> &'static str {
		match *self {
			Ty::Named(..) => "named type",
			Ty::Null => "null type",
			Ty::Int(_) | Ty::UnboundedInt => "integer type",
			Ty::Enum(_) => "enumeration type",
			Ty::Access(_) => "access type",
		}
	}
}

impl From<IntTy> for Ty {
	fn from(t: IntTy) -> Ty {
		Ty::Int(t)
	}
}

impl From<EnumTy> for Ty {
	fn from(t: EnumTy) -> Ty {
		Ty::Enum(t)
	}
}


/// An integer type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntTy {
	pub dir: Dir,
	pub left_bound: BigInt,
	pub right_bound: BigInt,
}

impl IntTy {
	/// Create a new integer type.
	pub fn new(dir: Dir, left_bound: BigInt, right_bound: BigInt) -> IntTy {
		IntTy {
			dir: dir,
			left_bound: left_bound,
			right_bound: right_bound,
		}
	}


	/// Map the type to itself if the range has a positive length, or to `null`
	/// if the range has a negative or zero length.
	pub fn maybe_null(self) -> Ty {
		match self.dir {
			Dir::To     if self.left_bound >= self.right_bound => Ty::Null,
			Dir::Downto if self.left_bound <= self.right_bound => Ty::Null,
			_ => self.into(),
		}
	}
}

impl fmt::Display for IntTy {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{} {} {}", self.left_bound, self.dir, self.right_bound)
	}
}


/// An enumeration type. Rather than keeping track of each enumeration value in
/// here, we simply point at the type declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumTy {
	pub decl: TypeDeclRef,
}

impl EnumTy {
	/// Create a new enumeration type.
	pub fn new(decl: TypeDeclRef) -> EnumTy {
		EnumTy {
			decl: decl,
		}
	}
}
