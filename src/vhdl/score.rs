// Copyright (c) 2017 Fabian Schuiki

//! This module implements the scoreboard that drives the compilation of VHDL.

#![allow(dead_code)]
#![allow(unused_imports)]

use std;
use std::collections::HashMap;
use std::cell::Cell;
use moore_common;
use moore_common::NodeId;
use syntax::ast;


/// The VHDL scoreboard that keeps track of compilation results.
pub struct Scoreboard<'ast, 'ctx> {
	/// A reference to the arenas where the scoreboard allocates nodes.
	arenas: &'ctx Arenas,
	/// An optional reference to a parent scoreboard.
	parent: Cell<Option<&'ctx moore_common::score::Scoreboard>>,
	/// The table of AST nodes.
	ast_table: AstTable<'ast>,
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
			ast_table: AstTable::new(),
		}
	}

	/// Change the parent scoreboard.
	pub fn set_parent(&self, parent: &'ctx moore_common::score::Scoreboard) {
		self.parent.set(Some(parent));
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


// Declare the node references.
node_ref!(DesignUnitRef);


// Declare the node tables.
node_storage!(AstTable,
	design_units: DesignUnitRef => ast::DesignUnit,
);
