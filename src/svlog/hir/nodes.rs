// Copyright (c) 2017 Fabian Schuiki

//! This module contains the nodes of the tree structure that is the HIR.

use std::collections::HashMap;
pub use common::name::Name;
pub use common::source::Span;
pub use ast::NodeId;
use ast;


// TODO: Take the AST expressions and split them into lvalue and rvalue
// expressions. This should make a few things easier.


/// The root of the HIR tree. This represents one elaborated design.
pub struct Root {
	pub top: NodeId,
	pub mods: HashMap<NodeId, Module>,
	pub intfs: HashMap<NodeId, Interface>,
	pub pkgs: HashMap<NodeId, Package>,
}

/// An search index of all nodes in a HIR tree.
pub struct NodeIndex<'hir> {
	pub hir: &'hir Root,
	pub nodes: HashMap<NodeId, Node<'hir>>,
}

#[derive(Copy, Clone)]
pub enum Node<'hir> {
	Module(&'hir Module),
	Interface(&'hir Interface),
	Package(&'hir Package),
	Port(&'hir Port),
	PortSlice(&'hir PortSlice),
	TypeParam(&'hir ast::ParamTypeDecl),
	ValueParam(&'hir ast::ParamValueDecl),
	VarDecl(&'hir ast::VarDecl, &'hir ast::VarDeclName),
}

/// A module.
pub struct Module {
	pub id: NodeId,
	pub name: Name,
	pub span: Span,
	pub lifetime: ast::Lifetime,
	pub ports: Vec<Port>,
	pub params: Vec<ast::ParamDecl>,
	pub body: HierarchyBody,
}

/// An interface.
pub struct Interface {
	pub id: NodeId,
	pub name: Name,
	pub span: Span,
	pub lifetime: ast::Lifetime,
	pub ports: Vec<Port>,
	pub params: Vec<ast::ParamDecl>,
	pub body: HierarchyBody,
}

/// A package.
pub struct Package {
	pub name: Name,
	pub span: Span,
	pub lifetime: ast::Lifetime,
	pub body: HierarchyBody,
}

/// A hierarchy body represents the contents of a module, interface, or package.
/// Generate regions and nested modules introduce additional bodies. The point
/// of hierarchy bodies is to take a level of the design hierarchy and group all
/// declarations by type, rather than having them in a single array in
/// declaration order.
pub struct HierarchyBody {
	pub procs: Vec<ast::Procedure>,
	pub nets: Vec<ast::NetDecl>,
	pub vars: Vec<ast::VarDecl>,
	pub assigns: Vec<ast::ContAssign>,
	pub params: Vec<ast::ParamDecl>,
	pub insts: Vec<ast::Inst>,
	pub genreg: Vec<HierarchyBody>,
	pub genvars: Vec<ast::GenvarDecl>,
	pub genfors: Vec<GenerateFor>,
	pub genifs: Vec<GenerateIf>,
	pub gencases: Vec<ast::GenerateCase>,
	pub classes: Vec<ast::ClassDecl>, // TODO: Make this an HIR node, since it contains hierarchy items
	pub subroutines: Vec<ast::SubroutineDecl>, // TODO: Make this an HIR node
	pub asserts: Vec<ast::Assertion>,
	pub typedefs: Vec<ast::Typedef>,
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
	pub id: NodeId,
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

pub struct GenerateBlock {
	pub span: Span,
	pub label: Option<Name>,
	pub body: HierarchyBody,
}

pub struct GenerateFor {
	pub span: Span,
	pub init: ast::Stmt,
	pub cond: ast::Expr,
	pub step: ast::Expr,
	pub block: GenerateBlock,
}

pub struct GenerateIf {
	pub span: Span,
	pub cond: ast::Expr,
	pub main_block: GenerateBlock,
	pub else_block: Option<GenerateBlock>,
}
