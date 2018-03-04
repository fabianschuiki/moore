// Copyright (c) 2017 Fabian Schuiki

//! This module implements VHDL types.

use std::fmt;
use std::collections::HashMap;
use std::cell::RefCell;

use num::{BigInt, One};

use common::source::Span;
use common::name::Name;
use score::*;
pub use hir::Dir;


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
	/// A named type. In a signal declaration for example, the source code
	/// mentions the type of the signal. This type name is resolved to its
	/// actual declaration somewhere else in the source code. Thus this type
	/// acts as a sort of "pointer" to a type, together with information on how
	/// the source code referred to that type. This helps make error messages
	/// easier to read for the user.
	Named(TyName, TypeMarkRef),
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
	/// A physical type.
	Physical(PhysicalTy),
	/// An access type.
	Access(Box<Ty>),
	/// An array type.
	Array(ArrayTy),
	/// A file type.
	File(Box<Ty>),
	/// A record type.
	Record(RecordTy),
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
			Ty::Physical(_) => "physical type",
			Ty::Access(_) => "access type",
			Ty::Array(_) => "array type",
			Ty::File(..) => "file type",
			Ty::Record(_) => "record type",
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

impl From<PhysicalTy> for Ty {
	fn from(t: PhysicalTy) -> Ty {
		Ty::Physical(t)
	}
}

impl From<ArrayTy> for Ty {
	fn from(t: ArrayTy) -> Ty {
		Ty::Array(t)
	}
}

impl From<RecordTy> for Ty {
	fn from(t: RecordTy) -> Ty {
		Ty::Record(t)
	}
}

impl fmt::Display for Ty {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Ty::Named(name, _) => write!(f, "{}", name),
			Ty::Null => write!(f, "null"),
			Ty::Int(ref ty) => write!(f, "{}", ty),
			Ty::UnboundedInt => write!(f, "{{integer}}"),
			Ty::Enum(ref ty) => write!(f, "{}", ty),
			Ty::Physical(ref ty) => write!(f, "{}", ty),
			Ty::Access(ref ty) => write!(f, "access {}", ty),
			Ty::Array(ref ty) => write!(f, "{}", ty),
			Ty::File(ref ty) => write!(f, "file of {}", ty),
			Ty::Record(ref ty) => write!(f, "{}", ty),
		}
	}
}

/// A type name.
///
/// Generally types are named by the source file. Builtin types on the other
/// hand have no span, but rather have an explicit name.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum TyName {
	/// A type name given by a section of a source file.
	Span(Span),
	/// A type name given by an explicit name.
	Name(Name),
}

impl fmt::Display for TyName {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			TyName::Span(span) => write!(f, "{}", span.extract()),
			TyName::Name(name) => write!(f, "{}", name),
		}
	}
}

impl From<Span> for TyName {
	fn from(span: Span) -> TyName {
		TyName::Span(span)
	}
}

impl From<Name> for TyName {
	fn from(name: Name) -> TyName {
		TyName::Name(name)
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

	/// The length of the range.
	pub fn len(&self) -> BigInt {
		match self.dir {
			Dir::To     => &self.left_bound + BigInt::one() - &self.right_bound,
			Dir::Downto => &self.right_bound + BigInt::one() - &self.left_bound,
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
	/// The declaration of the enum.
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

/// A physical type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhysicalTy {
	/// The declaration of the physical type.
	pub decl: TypeDeclRef,
	/// The underlying integer type.
	pub base: IntTy,
	/// The table of units.
	pub units: Vec<PhysicalUnit>,
	/// The index of the primary unit.
	pub primary: usize,
}

impl PhysicalTy {
	/// Create a new physical type.
	pub fn new(decl: TypeDeclRef, base: IntTy, units: Vec<PhysicalUnit>, primary: usize) -> PhysicalTy {
		PhysicalTy {
			decl: decl,
			base: base,
			units: units,
			primary: primary,
		}
	}
}

impl fmt::Display for PhysicalTy {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{} units ({})",
			self.base,
			DisplayList(RefCell::new(self.units.iter().map(|u| u.name)), Some(&","), Some(&", "), Some(&", ")),
		)
	}
}

/// A unit of a physical type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhysicalUnit {
	/// The name of the unit.
	pub name: Name,
	/// The scale of the unit with respect to the physical type's primary unit.
	pub abs: BigInt,
	/// The scale of the unit with respect to another unit.
	pub rel: Option<(BigInt, usize)>,
}

impl PhysicalUnit {
	/// Create a new unit for a physical type.
	pub fn new(name: Name, abs: BigInt, rel: Option<(BigInt, usize)>) -> PhysicalUnit {
		PhysicalUnit {
			name: name,
			abs: abs,
			rel: rel,
		}
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
			DisplayList(RefCell::new(self.indices.iter()), Some(&","), Some(&", "), Some(&", ")),
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

impl ArrayIndex {
	/// Get the type of the array index, regardless of its boundedness.
	pub fn ty(&self) -> &Ty {
		match *self {
			ArrayIndex::Unbounded(ref ty) => ty.as_ref(),
			ArrayIndex::Constrained(ref ty) => ty.as_ref(),
		}
	}
}

/// A record type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordTy {
	/// The fields of the record.
	pub fields: Vec<(Name, Box<Ty>)>,
	/// A lookup table to access fields by name.
	pub lookup: HashMap<Name, usize>,
}

impl RecordTy {
	/// Create a new array type.
	pub fn new(fields: Vec<(Name, Box<Ty>)>) -> RecordTy {
		let lookup = fields.iter().enumerate().map(|(i,&(n,_))| (n,i)).collect();
		RecordTy {
			fields: fields,
			lookup: lookup,
		}
	}
}

impl fmt::Display for RecordTy {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "record")?;
		if self.fields.is_empty() {
			return Ok(());
		}
		write!(f, "\n")?;
		for &(name, ref field) in &self.fields {
			let indented = format!("{}", field).replace('\n', "\n    ");
			write!(f, "   {}: {};\n", name, indented)?;
		}
		write!(f, "end record")?;
		Ok(())
	}
}

pub struct DisplayList<'a, T: 'a> (RefCell<T>, Option<&'a fmt::Display>, Option<&'a fmt::Display>, Option<&'a fmt::Display>);

impl<'a, T, I> fmt::Display for DisplayList<'a, T>
	where T: Iterator<Item=I>, I: fmt::Display
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		let mut iter = self.0.borrow_mut();
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
			write!(f, "{}", last)?;
			last = x;
			had_separator = true;
		}
		if !had_separator {
			if let Some(sep) = self.2 {
				write!(f, "{}", sep)?;
			}
		} else {
			if let Some(con) = self.3 {
				write!(f, "{}", con)?;
			}
		}
		write!(f, "{}", last)?;
		Ok(())
	}
}
