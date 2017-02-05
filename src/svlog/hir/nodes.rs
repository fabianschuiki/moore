// Copyright (c) 2017 Fabian Schuiki

//! This module contains the nodes of the tree structure that is the HIR.

use std::collections::HashMap;
pub use moore_common::name::Name;
pub use moore_common::source::Span;
pub use moore_svlog_syntax::ast::NodeId;


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
}

pub struct Interface {

}

pub struct Package {

}
