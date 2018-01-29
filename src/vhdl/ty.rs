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
	/// An array type.
	Array(ArrayTy),
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
			Ty::Array(_) => "array type",
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

impl From<ArrayTy> for Ty {
	fn from(t: ArrayTy) -> Ty {
		Ty::Array(t)
	}
}

impl fmt::Display for Ty {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Ty::Named(span, _) => write!(f, "{}", span.extract()),
			Ty::Null => write!(f, "null"),
			Ty::Int(ref ty) => write!(f, "{}", ty),
			Ty::UnboundedInt => write!(f, "{{integer}}"),
			Ty::Enum(ref ty) => write!(f, "{}", ty),
			Ty::Access(ref ty) => write!(f, "access {}", ty),
			Ty::Array(ref ty) => write!(f, "{}", ty),
		}
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

impl fmt::Display for EnumTy {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		// TODO: It should be possible somehow to print better information here.
		//       Maybe if we make `Ty` aware of its own internalization we could
		//       assign additional user-facing metadata, e.g. a variant list.
		write!(f, "enum")
	}
}


/// An array type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayTy {
	/// The index types of the array, at least one.
	pub indices: Vec<ArrayIndex>,
	/// The type of the array element.
	pub element: Box<Ty>,
}

impl ArrayTy {
	/// Create a new array type.
	pub fn new(indices: Vec<ArrayIndex>, element: Box<Ty>) -> ArrayTy {
		assert!(indices.len() > 0);
		ArrayTy {
			indices: indices,
			element: element,
		}
	}
}

impl fmt::Display for ArrayTy {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "array ({}) of {}",
			DisplayList(self.indices.iter(), Some(&","), None),
			self.element
		)
	}
}

/// An index type of an array type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArrayIndex {
	/// An unbounded index of the form `<type_mark> range <>`.
	Unbounded(Box<Ty>),
	/// A constrained index of the form `range ...`.
	Constrained(Box<Ty>),
}

impl fmt::Display for ArrayIndex {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			ArrayIndex::Unbounded(ref ty) => write!(f, "{} range <>", ty),
			ArrayIndex::Constrained(ref ty) => write!(f, "{}", ty),
		}
	}
}

pub struct DisplayList<'a, T> (T, Option<&'a fmt::Display>, Option<&'a fmt::Display>);

impl<'a, T, I> fmt::Display for DisplayList<'a, T>
	where T: Iterator<Item=I> + Clone, I: fmt::Display
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		let mut iter = self.0.clone();
		match iter.next() {
			Some(x) => write!(f, "{}", x)?,
			None => return Ok(()),
		}
		let mut last = match iter.next() {
			Some(x) => x,
			None => return Ok(()),
		};
		let mut had_separator = false;
		while let Some(x) = iter.next() {
			if let Some(sep) = self.1 {
				write!(f, "{}", sep)?;
			}
			write!(f, " {}", last)?;
			last = x;
			had_separator = true;
		}
		if had_separator {
			if let Some(sep) = self.1 {
				write!(f, "{}", sep)?;
			}
		}
		if let Some(con) = self.2 {
			write!(f, " {}", con)?;
		}
		write!(f, " {}", last)?;
		Ok(())
	}
}
