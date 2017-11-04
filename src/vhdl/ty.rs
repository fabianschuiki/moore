// Copyright (c) 2017 Fabian Schuiki

//! This module implements VHDL types.

use std::fmt;
use score::*;
use moore_common::source::Span;
use num::BigInt;
pub use hir::Dir;


#[derive(Debug, Clone)]
pub enum Ty {
	/// A named type. In a signal declaration for example, the source code
	/// mentions the type of the signal. This type name is resolved to its
	/// actual declaration somewhere else in the source code. Thus this type
	/// acts as a sort of "pointer" to a type, together with information on how
	/// the source code referred to that type. This helps make error messages
	/// easier to read for the user.
	Named(Span, TypeMarkRef),
	/// An integer type.
	Int(IntTy),
}


impl Ty {
	/// Provide a textual description of the kind of type. For example, if
	/// called on an integer type, the result is `"integer type"`, without any
	/// information on the exact nature of the integer.
	pub fn kind_desc(&self) -> &'static str {
		match *self {
			Ty::Named(..) => "named type",
			Ty::Int(_) => "integer type",
		}
	}
}


impl From<IntTy> for Ty {
	fn from(t: IntTy) -> Ty {
		Ty::Int(t)
	}
}


#[derive(Debug, Clone)]
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
}


impl fmt::Display for IntTy {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{} {} {}", self.left_bound, self.dir, self.right_bound)
	}
}
