// Copyright (c) 2016 Fabian Schuiki

use source::Span;
use name::Name;


pub struct ModDecl {
	name: Name,
	name_span: Span,
	span: Span,
}

pub struct IntfDecl {
	pub name: Name,
	pub name_span: Span,
	pub span: Span,
}
