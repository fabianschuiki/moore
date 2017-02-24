// Copyright (c) 2017 Fabian Schuiki

//! This module contains the nodes of the tree structure that is the HIR.

use std::collections::HashMap;
pub use moore_common::name::Name;
pub use moore_common::source::Span;
pub use moore_svlog_syntax::ast::NodeId;
use moore_svlog_syntax::ast;


/// The root of the HIR tree. This represents one elaborated design.
pub struct Root {
	pub top: NodeId,
	pub mods: HashMap<NodeId, Module>,
	pub intfs: HashMap<NodeId, Interface>,
	pub pkgs: HashMap<NodeId, Package>,
}

pub struct Module {
	pub name: Name,
	pub span: Span,
	pub ports: Vec<Port>,
}

pub struct Interface {

}

pub struct Package {

}

#[derive(Debug)]
pub struct Port {
	pub name: Option<Name>,
	pub span: Span,
	pub slices: Vec<PortSlice>,
}

/// A port slice refers to a port declaration within the module. It consists of
/// the name of the declaration and a list of optional member and index accesses
/// that select individual parts of the declaration.
#[derive(Debug)]
pub struct PortSlice {
	pub name: Name,
	pub span: Span,
	pub selects: Vec<PortSelect>,
	pub dir: ast::PortDir,
	pub kind: ast::PortKind,
	pub ty: Option<ast::Type>,
	pub dims: Vec<ast::TypeDim>,

}

#[derive(Debug)]
pub enum PortSelect {
	Member(Span, Name),
	Index(Span, Expr),
}

pub struct PortDecl {
	pub dir: ast::PortDir,
}

// pub enum PortDir {

// }

#[derive(Debug)]
pub struct Expr;
