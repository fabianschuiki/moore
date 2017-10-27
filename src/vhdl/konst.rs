// Copyright (c) 2017 Fabian Schuiki

//! This module implements constant value calculation for VHDL.

use num::BigInt;


/// A constant value.
#[derive(Debug)]
pub enum Const {
	Int(ConstInt),
	Float(ConstFloat),
}


impl Const {
	pub fn negate(&self) -> Const {
		match *self {
			Const::Int(ref c) => Const::Int(c.negate()),
			Const::Float(ref c) => Const::Float(c.negate()),
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


/// A constant integer value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstInt {
	pub value: BigInt,
}


impl ConstInt {
	/// Create a new constant integer.
	pub fn new(value: BigInt) -> ConstInt {
		ConstInt {
			value: value
		}
	}

	pub fn negate(&self) -> ConstInt {
		ConstInt::new(-self.value.clone())
	}
}


/// A constant float value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstFloat {
}


impl ConstFloat {
	pub fn negate(&self) -> ConstFloat {
		ConstFloat{}
	}
}
