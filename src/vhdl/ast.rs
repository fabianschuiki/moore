// Copyright (c) 2016 Fabian Schuiki

use name::Name;

pub struct DesignUnit {

}

pub enum ContextClause {
	Library(Vec<Name>),
	Use(Vec<Name>),
}


#[derive(Debug)]
pub struct Entity {
	name: Box<str>
}

#[derive(Debug)]
pub enum IntfDecl {
	None
}

#[derive(Debug)]
pub enum Mode {
	In,
	Out,
	Inout,
	Buffer,
	Linkage,
}

#[derive(Debug)]
pub struct SubtypeIndication {
	name: Name,
	constraint: Option<()>,
}

#[derive(Debug)]
pub struct EnumLiteral{}

#[derive(Debug)]
pub struct SubtypeDecl{}

#[derive(Debug)]
pub struct TypeDef{}

#[derive(Debug)]
pub struct TypeDecl{}

#[derive(Debug)]
pub struct Decl{}

#[derive(Debug)]
pub struct Expr{}

#[derive(Debug)]
pub enum Direction {
	In,
	Out
}

