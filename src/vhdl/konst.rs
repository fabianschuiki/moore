// Copyright (c) 2017 Fabian Schuiki

//! This module implements constant value calculation for VHDL.

use std::fmt;
use num::BigInt;
use ty::*;
use score::TypeDeclRef;
pub use hir::Dir;


/// A constant value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Const {
	Null,
	Int(ConstInt),
	Float(ConstFloat),
	Enum(ConstEnum),
	IntRange(ConstIntRange),
	FloatRange(ConstFloatRange),
}

impl Const {
	pub fn negate(self) -> Const {
		match self {
			Const::Null => panic!("cannot negate null"),
			Const::Int(c) => Const::Int(c.negate()),
			Const::Float(c) => Const::Float(c.negate()),
			Const::Enum(_) => panic!("cannot negate enumeration literal"),
			Const::IntRange(_) => panic!("cannot negate integer range"),
			Const::FloatRange(_) => panic!("cannot negate float range"),
		}
	}


	/// Provide a textual description of the kind of constant.
	pub fn kind_desc(&self) -> &'static str {
		match *self {
			Const::Null => "null",
			Const::Int(_) => "integer",
			Const::Float(_) => "float",
			Const::Enum(_) => "enumeration literal",
			Const::IntRange(_) => "integer range",
			Const::FloatRange(_) => "float range",
		}
	}
}

impl From<ConstInt> for Const {
	fn from(k: ConstInt) -> Const {
		Const::Int(k)
	}
}

impl From<ConstFloat> for Const {
	fn from(k: ConstFloat) -> Const {
		Const::Float(k)
	}
}

impl From<ConstEnum> for Const {
	fn from(k: ConstEnum) -> Const {
		Const::Enum(k)
	}
}

impl From<ConstIntRange> for Const {
	fn from(k: ConstIntRange) -> Const {
		Const::IntRange(k)
	}
}

impl From<ConstFloatRange> for Const {
	fn from(k: ConstFloatRange) -> Const {
		Const::FloatRange(k)
	}
}


/// A constant integer value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstInt {
	/// The type of the constant. If `None`, the constant is assumed to be an
	/// unbounded integer which cannot be mapped to LLHD.
	pub ty: Option<IntTy>,
	/// The value of the constant.
	pub value: BigInt,
}

impl ConstInt {
	/// Create a new constant integer.
	pub fn new(ty: Option<IntTy>, value: BigInt) -> ConstInt {
		ConstInt {
			ty: ty,
			value: value,
		}
	}

	pub fn negate(self) -> ConstInt {
		ConstInt::new(self.ty, -self.value)
	}
}


/// A constant float value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstFloat {
}

impl ConstFloat {
	pub fn negate(self) -> ConstFloat {
		ConstFloat{}
	}
}


/// A constant enumeration value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstEnum {
	/// The type declaration which declared the enum.
	pub decl: TypeDeclRef,
	/// The index of the literal.
	pub index: usize,
}

impl ConstEnum {
	/// Create a new constant integer.
	pub fn new(decl: TypeDeclRef, index: usize) -> ConstEnum {
		ConstEnum {
			decl: decl,
			index: index,
		}
	}
}


/// A constant range value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstRange<T: fmt::Display + fmt::Debug> {
	pub dir: Dir,
	pub left_bound: T,
	pub right_bound: T,
}

impl<T> ConstRange<T> where T: fmt::Display + fmt::Debug {
	/// Create a new constant range.
	pub fn new(dir: Dir, left_bound: T, right_bound: T) -> ConstRange<T> {
		ConstRange {
			dir: dir,
			left_bound: left_bound,
			right_bound: right_bound,
		}
	}
}

pub type ConstIntRange = ConstRange<ConstInt>;
pub type ConstFloatRange = ConstRange<ConstFloat>;


// ----- FORMATTING ------------------------------------------------------------

impl fmt::Display for Const {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Const::Null => write!(f, "null"),
			Const::Int(ref k) => k.fmt(f),
			Const::Float(ref k) => k.fmt(f),
			Const::Enum(ref k) => k.fmt(f),
			Const::IntRange(ref k) => k.fmt(f),
			Const::FloatRange(ref k) => k.fmt(f),
		}
	}
}

impl fmt::Display for ConstInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.value.fmt(f)
	}
}

impl fmt::Display for ConstEnum {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "<enum>")
	}
}

impl fmt::Display for ConstFloat {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "<float>")
	}
}

impl<T> fmt::Display for ConstRange<T> where T: fmt::Display + fmt::Debug {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{} {} {}", self.left_bound, self.dir, self.right_bound)
	}
}
