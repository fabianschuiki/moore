// Copyright (c) 2016 Fabian Schuiki

use source::Span;
use name::Name;


pub struct ModDecl {
	pub name: Name,
	pub name_span: Span,
	pub span: Span,
}

pub struct IntfDecl {
	pub name: Name,
	pub name_span: Span,
	pub span: Span,
}



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
	pub span: Span,
	pub data: TypeData,
	pub sign: TypeSign,
	pub dims: Vec<TypeDim>,
}

pub use self::TypeData::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeData {
	ImplicitType,
	NamedType(Name),

	// Integer Vector Types
	BitType,
	LogicType,
	RegType,

	// Integer Atom Types
	ByteType,
	ShortIntType,
	IntType,
	LongIntType,
	TimeType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeSign {
	None,
	Signed,
	Unsigned,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDim {
	Expr,
	Range,
	Queue,
	Unsized,
	Associative,
}
