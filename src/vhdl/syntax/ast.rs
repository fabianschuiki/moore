// Copyright (c) 2017 Fabian Schuiki

//! This module implements an abstract syntax tree for VHDL. It is emitted by
//! the parser.

use std;
use moore_common::source::{Span, Spanned};
use moore_common::name::Name;


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

#[derive(Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct CompoundName {
	pub id: NodeId,
	pub span: Span,
	pub primary: PrimaryName,
	pub parts: Vec<NamePart>,
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
	Attribute(Spanned<Name>, Option<Signature>),
	Call(AssocList),
}



// TODO
#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct AssocList;
#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Signature;
