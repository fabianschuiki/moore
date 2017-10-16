// Copyright (c) 2017 Fabian Schuiki

//! This module implements the scoreboard that drives the compilation of VHDL.

#![allow(dead_code)]
#![allow(unused_imports)]

use std;
use std::fmt::Debug;
use std::collections::HashMap;
use std::cell::{RefCell, Cell};
use moore_common;
use moore_common::name::*;
use moore_common::errors::*;
use moore_common::NodeId;
use moore_common::score::{NodeStorage, NodeMaker, Result};
use syntax::ast;


/// The VHDL scoreboard that keeps track of compilation results.
pub struct Scoreboard<'ast, 'ctx> {
	/// A reference to the arenas where the scoreboard allocates nodes.
	arenas: &'ctx Arenas,
	/// An optional reference to a parent scoreboard.
	parent: Cell<Option<&'ctx moore_common::score::Scoreboard>>,
	/// A table of library nodes. This is a filtered version of what the global
	/// scoreboard has, with only the VHDL nodes remaining.
	libs: HashMap<LibRef, Vec<&'ast ast::DesignUnit>>,
	/// A table of AST nodes.
	ast_table: RefCell<AstTable<'ast>>,
	/// A table of HIR nodes.
	hir_table: RefCell<HirTable<'ctx>>,
	/// A table of definitions in each scope.
	def_table: RefCell<HashMap<ScopeRef, &'ctx Scope>>,
}


impl<'ast, 'ctx> Scoreboard<'ast, 'ctx> {
	/// Creates a new empty VHDL scoreboard.
	///
	/// # Example
	/// ```
	/// use moore_vhdl::score::{Arenas, Scoreboard};
	///
	/// let arenas = Arenas::new();
	/// let sb = Scoreboard::new(&arenas);
	/// ```
	pub fn new(arenas: &'ctx Arenas) -> Scoreboard<'ast, 'ctx> {
		Scoreboard {
			arenas: arenas,
			parent: Cell::new(None),
			libs: HashMap::new(),
			ast_table: RefCell::new(AstTable::new()),
			hir_table: RefCell::new(HirTable::new()),
			def_table: RefCell::new(HashMap::new()),
		}
	}

	/// Change the parent scoreboard.
	pub fn set_parent(&self, parent: &'ctx moore_common::score::Scoreboard) {
		self.parent.set(Some(parent));
	}

	/// Add a library of AST nodes. This function is called by the global
	/// scoreboard to add VHDL-specific AST nodes.
	pub fn add_library(&mut self, id: LibRef, lib: Vec<&'ast ast::DesignUnit>) {
		if self.libs.insert(id, lib).is_some() {
			panic!("library did already exist");
		}
	}

	pub fn hir<I>(&self, id: I) -> Result<&'ctx <HirTable<'ctx> as NodeStorage<'ctx, I>>::Node> where
		I: 'ctx + Copy + Debug,
		HirTable<'ctx>: NodeStorage<'ctx, I>,
		Scoreboard<'ast, 'ctx>: NodeMaker<'ctx, I, <HirTable<'ctx> as NodeStorage<'ctx, I>>::Node>,
		<HirTable<'ctx> as NodeStorage<'ctx, I>>::Node: Debug {

		if let Some(node) = self.hir_table.borrow().get(&id) {
			return Ok(node);
		}
		let node = self.make(id)?;
		self.hir_table.borrow_mut().set(id, node);
		Ok(node)
	}

	pub fn defs(&self, id: ScopeRef) -> Result<&'ctx Scope> {
		if let Some(&s) = self.def_table.borrow().get(&id) {
			return Ok(s);
		}
		let s = self.make(id)?;
		self.def_table.borrow_mut().insert(id, s).is_some();
		Ok(s)
	}
}


impl<'ast, 'ctx> NodeMaker<'ctx, ScopeRef, Scope> for Scoreboard<'ast, 'ctx> {
	fn make(&self, id: ScopeRef) -> Result<&'ctx Scope> {
		println!("[SB][VHDL] trying to make scope {:?}", id);
		match id {
			ScopeRef::Lib(id) => {
				// Approach:
				// 1) Get the HIR of the library
				// 2) Gather definitions from the HIR.
				// 3) Create scope and return.
				let lib = self.hir(id)?;
				unimplemented!("defs for lib {:?}", id);
			}
		}
	}
}


impl<'ast, 'ctx> NodeMaker<'ctx, LibRef, hir::Lib> for Scoreboard<'ast, 'ctx> {
	fn make(&self, id: LibRef) -> Result<&'ctx hir::Lib> {
		println!("[SB][VHDL] make hir for lib {:?}", id);
		unimplemented!("hir for lib {:?}", id);
	}
}


/// A collection of arenas that the scoreboard uses to allocate its nodes.
pub struct Arenas {
}


impl Arenas {
	/// Create a new set of arenas.
	pub fn new() -> Arenas {
		Arenas {

		}
	}
}


/// A set of names and definitions.
pub type Scope = HashMap<Name, Vec<Def>>;


// Declare the node references.
node_ref!(LibRef);
node_ref!(DesignUnitRef);

// Declare the node reference groups.
node_ref_group!(Def: Lib(LibRef));
node_ref_group!(ScopeRef: Lib(LibRef));


// Declare the node tables.
node_storage!(AstTable,
	design_units: DesignUnitRef => ast::DesignUnit,
);

node_storage!(HirTable,
	libs: LibRef => hir::Lib,
);


pub mod hir {
	#[derive(Debug)]
	pub struct Lib {

	}
}
