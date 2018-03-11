// Copyright (c) 2017 Fabian Schuiki

//! This module implements an abstract syntax tree for VHDL. It is emitted by
//! the parser.

use std;
use std::fmt;

use moore_common::source::{Span, Spanned};
use moore_common::name::Name;
use moore_common::util::{HasSpan, HasDesc};
use lexer::token::Literal;

pub use self::ExprData::*;
pub use self::TypeData::*;
pub use self::StmtData::*;


/// A positive, small ID assigned to each node in the AST. Used as a lightweight
/// way to refer to individual nodes, e.g. during symbol table construction and
/// name resolution.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash, Debug, RustcEncodable, RustcDecodable)]
pub struct NodeId(u32);

impl NodeId {
    pub fn new(x: usize) -> NodeId {
		use std::u32;
        assert!(x < (u32::MAX as usize));
        NodeId(x as u32)
    }

    pub fn from_u32(x: u32) -> NodeId {
        NodeId(x)
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    pub fn as_u32(&self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Default for NodeId {
	fn default() -> NodeId {
		DUMMY_NODE_ID
	}
}

/// During parsing and syntax tree construction, we assign each node this ID.
/// Only later, during the renumbering pass do we assign actual IDs to each
/// node.
pub const DUMMY_NODE_ID: NodeId = NodeId(0);



/// A design unit. Multiple design units make up a design file. Each unit
/// consists of an optional context clause followed by a primary or secondary
/// unit.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct DesignUnit {
	pub id: NodeId,
	pub ctx: Vec<CtxItem>,
	pub data: DesignUnitData,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum DesignUnitData {
	EntityDecl(EntityDecl),
	CfgDecl(CfgDecl),
	PkgDecl(PkgDecl),
	PkgInst(PkgInst),
	CtxDecl(CtxDecl),
	ArchBody(ArchBody),
	PkgBody(PkgBody),
}

/// A context item, multiple of which make up a context clause.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum CtxItem {
	LibClause(Spanned<Vec<Ident>>),
	UseClause(Spanned<Vec<CompoundName>>),
	CtxRef(Spanned<Vec<CompoundName>>),
}

/// An identifier. Has a node ID such that it may be referenced later on.
#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
// #[deprecated(note="use `Spanned<Name>` instead of `Ident`")]
pub struct Ident {
	pub id: NodeId,
	pub span: Span,
	pub name: Name,
}

impl From<Spanned<Name>> for Ident {
	fn from(n: Spanned<Name>) -> Ident {
		Ident{
			id: Default::default(),
			span: n.span,
			name: n.value,
		}
	}
}

impl Into<Spanned<Name>> for Ident {
	fn into(self) -> Spanned<Name> {
		Spanned::new(self.name, self.span)
	}
}


/// A compound name consisting of a primary name (identifier, character literal,
/// or string literal), and zero or more suffices (select, attribute, call). The
/// names in *IEEE 1076-2008 section 8.1* map to this as follows:
///
/// | In the standard     | In this module                  |
/// |---------------------|---------------------------------|
/// | simple_name         | `PrimaryNameKind::Ident`        |
/// | operator_symbol     | `PrimaryNameKind::String`       |
/// | character_literal   | `PrimaryNameKind::Char`         |
/// | selected_name       | `NamePart::{Select, SelectAll}` |
/// | indexed_name        | `NamePart::Call`                |
/// | slice_name          | `NamePart::Call`                |
/// | function_call       | `NamePart::Call`                |
/// | attribute_name      | `NamePart::Attribute`           |
/// | external_name       | not implemented                 |
///
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct CompoundName {
	pub id: NodeId,
	pub span: Span,
	pub primary: PrimaryName,
	pub parts: Vec<NamePart>,
}

impl HasSpan for CompoundName {
	fn span(&self) -> Span {
		self.span
	}
}

impl HasDesc for CompoundName {
	fn desc(&self) -> &'static str {
		"name"
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct PrimaryName {
	pub id: NodeId,
	pub span: Span,
	pub kind: PrimaryNameKind,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum PrimaryNameKind {
	Ident(Name),
	Char(char),
	String(Name),
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum NamePart {
	Select(PrimaryName),
	SelectAll(Span),
	Signature(Signature),
	Attribute(Ident),
	Call(ParenElems),
	Range(Box<Expr>),
}


/// A context declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct CtxDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub items: Vec<CtxItem>,
}

/// An entity declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct EntityDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub decls: Vec<DeclItem>,
	pub stmts: Option<Vec<Stmt>>,
}

/// A configuration declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct CfgDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub target: CompoundName,
	pub decls: Vec<DeclItem>,
}

/// An architecture body.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ArchBody {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub target: CompoundName,
	pub decls: Vec<DeclItem>,
	pub stmts: Vec<Stmt>,
}

/// A package declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct PkgDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub decls: Vec<DeclItem>,
}

/// A package body.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct PkgBody {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub decls: Vec<DeclItem>,
}

/// A package instantiation declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct PkgInst {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub target: CompoundName,
	pub generics: Option<ParenElems>,
}


/// An interface declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum IntfDecl {
	TypeDecl(TypeDecl),
	SubprogSpec(IntfSubprogDecl),
	PkgInst(PkgInst),
	ObjDecl(IntfObjDecl),
}

impl HasSpan for IntfDecl {
	fn span(&self) -> Span {
		match *self {
			IntfDecl::TypeDecl(ref n) => n.span,
			IntfDecl::SubprogSpec(ref n) => n.span,
			IntfDecl::PkgInst(ref n) => n.span,
			IntfDecl::ObjDecl(ref n) => n.span,
		}
	}

	fn human_span(&self) -> Span {
		match *self {
			IntfDecl::TypeDecl(ref n) => n.name.span,
			IntfDecl::PkgInst(ref n) => n.name.span,
			_ => self.span()
		}
	}
}

impl HasDesc for IntfDecl {
	fn desc(&self) -> &'static str {
		match *self {
			IntfDecl::TypeDecl(_) => "interface type declaration",
			IntfDecl::SubprogSpec(_) => "interface subprogram declaration",
			IntfDecl::PkgInst(_) => "interface package declaration",
			IntfDecl::ObjDecl(ref n) => n.desc(),
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct IntfSubprogDecl {
	pub id: NodeId,
	pub span: Span,
	pub spec: SubprogSpec,
	pub default: Option<SubprogDefault>,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SubprogDefault {
	Any,
	Name(CompoundName),
}

/// An interface object declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct IntfObjDecl {
	pub kind: IntfObjKind,
	pub span: Span,
	pub names: Vec<Ident>,
	pub mode: Option<IntfMode>,
	pub ty: SubtypeInd,
	pub bus: bool,
	pub default: Option<Expr>,
}

impl HasDesc for IntfObjDecl {
	fn desc(&self) -> &'static str {
		match self.kind {
			IntfObjKind::Const => "interface constant declaration",
			IntfObjKind::Signal => "interface signal declaration",
			IntfObjKind::Var => "interface variable declaration",
			IntfObjKind::File => "interface file declaration",
		}
	}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum IntfObjKind {
	Const,
	Signal,
	Var,
	File,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum IntfMode {
	In,
	Out,
	Inout,
	Buffer,
	Linkage,
}

/// A declarative item.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum DeclItem {
	PkgBody(PkgBody),
	PkgInst(PkgInst),
	PkgDecl(PkgDecl),
	TypeDecl(TypeDecl),
	SubtypeDecl(SubtypeDecl),
	ObjDecl(ObjDecl),
	AliasDecl(AliasDecl),
	UseClause(Span, Spanned<Vec<CompoundName>>),
	SubprogDecl(Subprog),
	CompDecl(CompDecl),
	DisconDecl(DisconSpec),
	CfgSpec(CfgSpec),
	AttrDecl(AttrDecl),
	PortgenMap(Span, Spanned<PortgenKind>, ParenElems),
	PortgenClause(Span, Spanned<PortgenKind>, Spanned<Vec<IntfDecl>>),
	GroupDecl(GroupDecl),
	VunitBindInd(()),
	BlockCompCfg(BlockCompCfg),
}

impl HasSpan for DeclItem {
	fn span(&self) -> Span {
		match *self {
			DeclItem::PkgBody(ref n) => n.span,
			DeclItem::PkgInst(ref n) => n.span,
			DeclItem::PkgDecl(ref n) => n.span,
			DeclItem::TypeDecl(ref n) => n.span,
			DeclItem::SubtypeDecl(ref n) => n.span,
			DeclItem::ObjDecl(ref n) => n.span,
			DeclItem::AliasDecl(ref n) => n.span,
			DeclItem::UseClause(sp, ref n) => Span::union(sp, n.span),
			DeclItem::SubprogDecl(ref n) => n.span(),
			DeclItem::CompDecl(ref n) => n.span,
			DeclItem::DisconDecl(ref n) => n.span,
			DeclItem::CfgSpec(ref n) => n.span,
			DeclItem::AttrDecl(ref n) => n.span,
			DeclItem::PortgenMap(sp, _, _) => sp,
			DeclItem::PortgenClause(sp, _, _) => sp,
			DeclItem::GroupDecl(ref n) => n.span,
			DeclItem::VunitBindInd(_) => unimplemented!(),
			DeclItem::BlockCompCfg(ref n) => n.span,
		}
	}

	fn human_span(&self) -> Span {
		match *self {
			DeclItem::PkgBody(ref n) => n.name.span,
			DeclItem::PkgInst(ref n) => n.name.span,
			DeclItem::PkgDecl(ref n) => n.name.span,
			DeclItem::TypeDecl(ref n) => n.name.span,
			DeclItem::SubtypeDecl(ref n) => n.name.span,
			DeclItem::AliasDecl(ref n) => n.name.span,
			DeclItem::UseClause(sp, _) => sp,
			DeclItem::SubprogDecl(ref n) => n.human_span(),
			DeclItem::PortgenMap(_, Spanned{ span, .. }, _) => span,
			DeclItem::PortgenClause(_, Spanned{ span, .. }, _) => span,
			_ => self.span()
		}
	}
}

impl HasDesc for DeclItem {
	fn desc(&self) -> &'static str {
		match *self {
			DeclItem::PkgBody(..)        => "package body",
			DeclItem::PkgInst(..)        => "package instance",
			DeclItem::PkgDecl(..)        => "package declaration",
			DeclItem::TypeDecl(..)       => "type declaration",
			DeclItem::SubtypeDecl(..)    => "subtype declaration",
			DeclItem::ObjDecl(..)        => "object declaration",
			DeclItem::AliasDecl(..)      => "alias declaration",
			DeclItem::UseClause(..)      => "use clause",
			DeclItem::SubprogDecl(ref n) => n.desc(),
			DeclItem::CompDecl(..)       => "component declaration",
			DeclItem::DisconDecl(..)     => "disconnection declaration",
			DeclItem::CfgSpec(..)        => "configuration specification",
			DeclItem::AttrDecl(..)       => "attribute declaration",
			DeclItem::PortgenMap(_, Spanned{ value: PortgenKind::Port, .. }, ..)       => "port map",
			DeclItem::PortgenMap(_, Spanned{ value: PortgenKind::Generic, .. }, ..)    => "generic map",
			DeclItem::PortgenClause(_, Spanned{ value: PortgenKind::Port, .. }, ..)    => "port clause",
			DeclItem::PortgenClause(_, Spanned{ value: PortgenKind::Generic, .. }, ..) => "generic clause",
			DeclItem::GroupDecl(..)      => "group declaration",
			DeclItem::VunitBindInd(..)   => "vunit binding indication",
			DeclItem::BlockCompCfg(..)   => "block component configuration",
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum PortgenKind {
	Port,
	Generic,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Subprog {
	pub id: NodeId,
	pub span: Span,
	pub spec: SubprogSpec,
	pub data: SubprogData,
}

impl HasSpan for Subprog {
	fn span(&self) -> Span {
		self.span
	}

	fn human_span(&self) -> Span {
		self.spec.name.span
	}
}

impl HasDesc for Subprog {
	fn desc(&self) -> &'static str {
		self.data.desc()
	}
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SubprogData {
	Decl,
	Inst {
		name: CompoundName,
		generics: Option<ParenElems>,
	},
	Body {
		decls: Vec<DeclItem>,
		stmts: Vec<Stmt>,
	},
}

impl HasDesc for SubprogData {
	fn desc(&self) -> &'static str {
		match *self {
			SubprogData::Decl => "subprogram declaration",
			SubprogData::Inst{..} => "subprogram instantiation",
			SubprogData::Body{..} => "subprogram body",
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SubprogSpec {
	pub span: Span,
	pub name: PrimaryName,
	pub kind: SubprogKind,
	pub purity: Option<SubprogPurity>,
	pub generic_clause: Option<Vec<IntfDecl>>,
	pub generic_map: Option<ParenElems>,
	pub params: Option<Vec<IntfDecl>>,
	pub retty: Option<CompoundName>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SubprogPurity {
	Pure,
	Impure,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SubprogKind {
	Proc,
	Func,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SubtypeInd {
	pub span: Span,
	pub res: Option<ResolInd>,
	pub name: CompoundName,
}

impl HasSpan for SubtypeInd {
	fn span(&self) -> Span {
		self.span
	}
}

impl HasDesc for SubtypeInd {
	fn desc(&self) -> &'static str {
		"subtype indication"
	}
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SubtypeDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub subtype: SubtypeInd,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ResolInd {
	Exprs(ParenElems),
	Name(CompoundName),
}

/// An alias declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct AliasDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: PrimaryName,
	pub subtype: Option<SubtypeInd>,
	pub target: CompoundName,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ObjDecl {
	pub span: Span,
	pub kind: ObjKind,
	pub names: Vec<Ident>,
	pub subtype: SubtypeInd,
	pub detail: Option<Spanned<ObjDetail>>,
	pub init: Option<Expr>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ObjKind {
	Const,
	Signal,
	File,
	Var,
	SharedVar,
}

/// Additional mutually exclusive details that may be provided with an object
/// declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ObjDetail {
	Register,
	Bus,
	/// A file opening action.
	Open(Option<Expr>, Expr),
}

impl HasSpan for ObjDecl {
	fn span(&self) -> Span {
		self.span
	}

	fn human_span(&self) -> Span {
		self.names.iter().map(|n| n.span).fold(self.names[0].span, Span::union)
	}
}

impl HasDesc for ObjDecl {
	fn desc(&self) -> &'static str {
		match self.kind {
			ObjKind::Const     => "constant declaration",
			ObjKind::Signal    => "signal declaration",
			ObjKind::File      => "file declaration",
			ObjKind::Var       => "variable declaration",
			ObjKind::SharedVar => "shared variable declaration",
		}
	}
}


/// A component declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct CompDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub generics: Option<Spanned<Vec<IntfDecl>>>,
	pub ports: Option<Spanned<Vec<IntfDecl>>>,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct DisconSpec {
	pub span: Span,
	pub target: DisconTarget,
	pub ty: CompoundName,
	pub after: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum DisconTarget {
	Others,
	All,
	Signals(Vec<CompoundName>),
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct BlockCompCfg {
	pub span: Span,
	pub spec: Spanned<BlockCompSpec>,
	pub bind: BindingInd,
	pub decls: Vec<DeclItem>,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum BlockCompSpec {
	CompOthers(CompoundName),
	CompAll(CompoundName),
	CompNames(Vec<Ident>, CompoundName),
	Block(CompoundName),
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct BindingInd{
	pub span: Span,
	pub entity: Option<EntityAspect>,
	pub generics: Option<ParenElems>,
	pub ports: Option<ParenElems>,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum EntityAspect {
	Entity(CompoundName),
	Cfg(CompoundName),
	Open,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct CfgSpec {
	pub span: Span,
	pub spec: Spanned<BlockCompSpec>,
	pub bind: BindingInd,
	pub vunits: Vec<()>,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct AttrDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub data: AttrData,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum AttrData {
	Decl(CompoundName),
	Spec {
		target: AttrTarget,
		cls: EntityClass,
		expr: Expr,
	}
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum AttrTarget {
	Others,
	All,
	List(Vec<(CompoundName, Option<Signature>)>),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum EntityClass {
	Arch,
	Comp,
	Cfg,
	Const,
	Entity,
	File,
	Func,
	Group,
	Label,
	Literal,
	Pkg,
	Proc,
	Prop,
	Seq,
	Signal,
	Subtype,
	Type,
	Units,
	Var,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct GroupDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub data: GroupData,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum GroupData {
	/// A group declaration.
	Decl(CompoundName),
	/// A group template. Each element consists of an entity class, and a bool
	/// that indicates whether a `<>` was present in the source text.
	Temp(Vec<(EntityClass, bool)>),
}

/// A parenthesized expression element. A parenthesized expression contains
/// elements of which each may either be a simple `<expr>`, or an association of
/// the form `<choices> => <expr>`.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ParenElem {
	pub span: Span,
	pub choices: Choices,
	pub expr: Expr,
}

/// A vector of parenthesized expression elements, including the span of the
/// expression that this would cover.
pub type ParenElems = Spanned<Vec<ParenElem>>;


/// An expression.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Expr {
	pub span: Span,
	pub data: ExprData,
}

impl HasSpan for Expr {
	fn span(&self) -> Span {
		self.span
	}
}

impl HasDesc for Expr {
	fn desc(&self) -> &'static str {
		self.data.desc()
	}
}

/// The data associated with a specific expression.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ExprData {
	NullExpr,
	OpenExpr,
	OthersExpr,
	DefaultExpr,
	BoxExpr,
	NewExpr(Box<Expr>),
	LitExpr(Literal, Option<Spanned<Name>>),
	ResolExpr(ParenElems, CompoundName),
	ParenExpr(ParenElems),
	DoubleNameExpr(CompoundName, CompoundName),
	QualExpr(CompoundName, ParenElems),
	NameExpr(CompoundName),
	UnaryExpr(UnaryOp, Box<Expr>),
	BinaryExpr(BinaryOp, Box<Expr>, Box<Expr>),
}

impl HasDesc for ExprData {
	fn desc(&self) -> &'static str {
		match *self {
			NullExpr => "null expression",
			UnaryExpr(..) => "unary expression",
			BinaryExpr(..) => "binary expression",
			_ => "expression",
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum UnaryOp {
	Not,
	Abs,
	Sign(Sign),
	Logical(LogicalOp),
	Inertial,
	Condition,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum BinaryOp {
	Dir(Dir),
	Logical(LogicalOp),
	Rel(RelationalOp),
	Match(RelationalOp),
	Shift(ShiftOp),
	Add,
	Sub,
	Concat,
	Mul,
	Div,
	Mod,
	Rem,
	Pow,
}


#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum Dir {
	To,
	Downto,
}

impl std::fmt::Display for Dir {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			Dir::To => write!(f, "to"),
			Dir::Downto => write!(f, "downto"),
		}
	}
}


#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum Sign {
	Pos,
	Neg,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum LogicalOp {
	And,
	Or,
	Nand,
	Nor,
	Xor,
	Xnor,
}

impl fmt::Display for LogicalOp {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			LogicalOp::And  => write!(f, "and"),
			LogicalOp::Or   => write!(f, "or"),
			LogicalOp::Nand => write!(f, "nand"),
			LogicalOp::Nor  => write!(f, "nor"),
			LogicalOp::Xor  => write!(f, "xor"),
			LogicalOp::Xnor => write!(f, "xnor"),
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum RelationalOp {
	Eq,
	Neq,
	Lt,
	Leq,
	Gt,
	Geq,
}

impl fmt::Display for RelationalOp {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			RelationalOp::Eq  => write!(f, "="),
			RelationalOp::Neq => write!(f, "/="),
			RelationalOp::Lt  => write!(f, "<"),
			RelationalOp::Leq => write!(f, "<="),
			RelationalOp::Gt  => write!(f, ">"),
			RelationalOp::Geq => write!(f, ">="),
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum ShiftOp {
	Sll,
	Srl,
	Sla,
	Sra,
	Rol,
	Ror,
}

impl fmt::Display for ShiftOp {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			ShiftOp::Sll => write!(f, "sll"),
			ShiftOp::Srl => write!(f, "srl"),
			ShiftOp::Sla => write!(f, "sla"),
			ShiftOp::Sra => write!(f, "sra"),
			ShiftOp::Rol => write!(f, "rol"),
			ShiftOp::Ror => write!(f, "ror"),
		}
	}
}


/// A type declaration. If the `data` field is omitted, this is an incomplete
/// declaration.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct TypeDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Spanned<Name>,
	pub data: Option<Spanned<TypeData>>,
}

impl HasSpan for TypeDecl {
	fn span(&self) -> Span {
		self.span
	}

	fn human_span(&self) -> Span {
		self.name.span
	}
}

impl HasDesc for TypeDecl {
	fn desc(&self) -> &'static str {
		match self.data {
			Some(ref d) => d.desc(),
			None => "incomplete type declaration",
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum TypeData {
	EnumType(ParenElems),
	RangeType(Box<Expr>, Option<Vec<(Ident, Option<Box<Expr>>)>>),
	ArrayType(ParenElems, SubtypeInd),
	RecordType(Vec<(Vec<Ident>, SubtypeInd)>),
	AccessType(SubtypeInd),
	FileType(CompoundName),
	ProtectedType(Vec<DeclItem>),
}

impl HasDesc for TypeData {
	fn desc(&self) -> &'static str {
		match *self {
			TypeData::EnumType(..) => "enumeration type declaration",
			TypeData::RangeType(..) => "range type declaration",
			TypeData::ArrayType(..) => "array type declaration",
			TypeData::RecordType(..) => "record type declaration",
			TypeData::AccessType(..) => "access type declaration",
			TypeData::FileType(..) => "file type declaration",
			TypeData::ProtectedType(..) => "protected type declaration",
		}
	}
}


#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Stmt {
	pub id: NodeId,
	pub span: Span,
	pub label: Option<Spanned<Name>>,
	pub data: StmtData,
}

impl HasSpan for Stmt {
	fn span(&self) -> Span {
		self.span
	}

	fn human_span(&self) -> Span {
		match self.label {
			Some(Spanned{ span, .. }) => span,
			_ => self.span()
		}
	}
}

impl HasDesc for Stmt {
	fn desc(&self) -> &'static str {
		self.data.desc()
	}
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum StmtData {
	WaitStmt {
		on: Option<Spanned<Vec<CompoundName>>>,
		until: Option<Expr>,
		time: Option<Expr>,
	},
	AssertStmt {
		cond: Expr,
		report: Option<Expr>,
		severity: Option<Expr>,
	},
	ReportStmt {
		msg: Expr,
		severity: Option<Expr>,
	},
	IfStmt {
		conds: Vec<(Expr, StmtBody)>,
		alt: Option<StmtBody>,
	},
	CaseStmt {
		qm: bool,
		switch: Expr,
		cases: Vec<(Choices, StmtBody)>,
	},
	LoopStmt {
		scheme: LoopScheme,
		body: StmtBody,
	},
	NexitStmt {
		mode: NexitMode,
		target: Option<Spanned<Name>>,
		cond: Option<Expr>,
	},
	ReturnStmt(Option<Expr>),
	NullStmt,
	IfGenStmt {
		conds: Vec<(Expr, GenBody)>,
		alt: Option<GenBody>,
	},
	CaseGenStmt {
		switch: Expr,
		cases: Vec<(Choices, GenBody)>,
	},
	ForGenStmt {
		param: Spanned<Name>,
		range: Expr,
		body: GenBody,
	},
	BlockStmt {
		guard: Option<Expr>,
		decls: Vec<DeclItem>,
		stmts: Vec<Stmt>,
	},
	ProcStmt {
		sensitivity: Option<Sensitivity>,
		decls: Vec<DeclItem>,
		stmts: Vec<Stmt>,
		postponed: bool,
	},
	AssignStmt {
		target: Spanned<AssignTarget>,
		kind: AssignKind,
		guarded: bool,
		mode: Spanned<AssignMode>,
	},
	SelectAssignStmt {
		select: Expr,
		qm: bool,
		target: Spanned<AssignTarget>,
		kind: AssignKind,
		guarded: bool,
		mode: SelectAssignMode,
		waves: Vec<SelectWave>,
	},
	InstOrCallStmt {
		target: Option<InstTarget>,
		name: CompoundName,
		generics: Option<ParenElems>,
		ports: Option<ParenElems>,
	},
}

impl HasDesc for StmtData {
	fn desc(&self) -> &'static str {
		match *self {
			StmtData::WaitStmt{..} => "wait statement",
			StmtData::AssertStmt{..} => "assertion statement",
			StmtData::ReportStmt{..} => "report statement",
			StmtData::IfStmt{..} => "if statement",
			StmtData::CaseStmt{..} => "case statement",
			StmtData::LoopStmt{..} => "loop statement",
			StmtData::NexitStmt{mode: NexitMode::Next, ..} => "next statement",
			StmtData::NexitStmt{mode: NexitMode::Exit, ..} => "exit statement",
			StmtData::ReturnStmt(..) => "return statement",
			StmtData::NullStmt => "null statement",
			StmtData::IfGenStmt{..} => "if-generate statement",
			StmtData::CaseGenStmt{..} => "case-generate statement",
			StmtData::ForGenStmt{..} => "for-generate statement",
			StmtData::BlockStmt{..} => "block statement",
			StmtData::ProcStmt{..} => "process statement",
			StmtData::AssignStmt{..} => "assign statement",
			StmtData::SelectAssignStmt{..} => "assign statement",
			StmtData::InstOrCallStmt{..} => "instantiation or call statement",
		}
	}
}

/// The body of an if, loop, or case statement.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct StmtBody {
	pub id: NodeId,
	pub stmts: Vec<Stmt>,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum LoopScheme {
	While(Expr),
	For(Spanned<Name>, Expr),
	Loop,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum NexitMode {
	Next,
	Exit,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct GenBody {
	pub id: NodeId,
	pub label: Option<Spanned<Name>>,
	pub span: Span,
	pub decls: Vec<DeclItem>,
	pub stmts: Vec<Stmt>,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum Sensitivity {
	All,
	List(Vec<CompoundName>),
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum AssignTarget {
	Name(CompoundName),
	Aggregate(ParenElems),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum InstTarget {
	Comp,
	Entity,
	Cfg,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum AssignKind {
	Signal,
	Var,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum AssignMode {
	Release(Option<Spanned<ForceMode>>),
	Force(Option<Spanned<ForceMode>>, Vec<CondWave>),
	Normal(Option<Spanned<DelayMech>>, Vec<CondWave>),
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SelectAssignMode {
	Force(Option<Spanned<ForceMode>>),
	Normal(Option<Spanned<DelayMech>>),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ForceMode {
	In,
	Out,
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum DelayMech {
	Transport,
	Inertial,
	InertialReject(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Wave {
	pub span: Span,
	pub elems: Option<Vec<(Expr, Option<Expr>)>>,
}

/// A conditional wave.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct CondWave(pub Wave, pub Option<Expr>);

/// A selected wave. The second element of the tuple represents the choices for
/// which this wave would be selected.
#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SelectWave(pub Wave, pub Choices);


#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Signature {
	pub span: Span,
	pub args: Vec<CompoundName>,
	pub retty: Option<CompoundName>,
}

pub type Choices = Spanned<Vec<Expr>>;
