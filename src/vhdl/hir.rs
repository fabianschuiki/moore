// Copyright (c) 2017 Fabian Schuiki

//! The High-level Intermediate Representation of a VHDL design.

use moore_common::source::*;
use moore_common::name::*;
use score::*;
use typed_arena::Arena;


/// A collection of arenas where HIR nodes may be allocated.
pub struct Arenas {
	pub lib: Arena<Lib>,
	pub entity: Arena<Entity>,
}


impl Arenas {
	/// Create a new set of arenas.
	pub fn new() -> Arenas {
		Arenas {
			lib: Arena::new(),
			entity: Arena::new(),
		}
	}
}


#[derive(Debug)]
pub struct Lib {
	pub entities: Vec<EntityRef>,
	pub cfgs: Vec<CfgRef>,
	pub pkg_decls: Vec<PkgDeclRef>,
	pub pkg_insts: Vec<PkgInstRef>,
	pub ctxs: Vec<CtxRef>,
	pub archs: Vec<ArchRef>,
	pub pkg_bodies: Vec<PkgBodyRef>,
}

impl Lib {
	pub fn new() -> Lib {
		Lib {
			entities: Vec::new(),
			cfgs: Vec::new(),
			pkg_decls: Vec::new(),
			pkg_insts: Vec::new(),
			ctxs: Vec::new(),
			archs: Vec::new(),
			pkg_bodies: Vec::new(),
		}
	}
}


#[derive(Debug)]
pub struct Entity {
	/// The library in which the entity is defined.
	pub lib: LibRef,
	/// The entity name.
	pub name: Spanned<Name>,
	/// The list of generics that the entity declares.
	pub generics: Vec<GenericRef>,
	/// The list of ports that the entity declares.
	pub ports: Vec<IntfSignalRef>,
}
