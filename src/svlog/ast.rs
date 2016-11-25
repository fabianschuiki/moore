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
