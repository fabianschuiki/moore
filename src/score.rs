// Copyright (c) 2017 Fabian Schuiki
#![allow(dead_code)]

//! This module implements the scoreboard. The scoreboard is where the compiler
//! keeps track of intermediate results and processed artifacts, and where
//! additional compilation steps are initiated. This enables on-demand
//! compilation.

use std;
use std::collections::HashMap;
use moore_common;
use moore_common::name::Name;
use moore_common::NodeId;
use moore_vhdl::syntax::ast as vhdl_ast;
use moore_vhdl as vhdl;
use moore_svlog::ast as svlog_ast;


pub type Result<T> = std::result::Result<T, ()>;


/// The global scoreboard that drives the compilation of pretty much anything.
pub struct Scoreboard<'ast, 'ctx> {
	/// The arenas within which the various nodes will be allocated.
	arenas: &'ctx Arenas,
	/// The root node ID, where the libraries live.
	pub root_id: NodeId,
	/// The next node ID to be assigned.
	next_id: usize,
	/// The VHDL scoreboard.
	vhdl: vhdl::score::Scoreboard<'ast, 'ctx>,
	/// A table of library nodes. This is the only node that is actively
	/// maintained by the global scoreboard.
	libs: HashMap<LibRef, &'ast [Ast]>,
	// /// A table of unprocessed AST nodes.
	// asts: HashMap<NodeId, Ast<'ast>>,
	// /// A table of processed HIR nodes.
	// hirs: HashMap<NodeId, &'ctx Hir>,
	// /// A table of definitions in each scope.
	// defs: HashMap<NodeId, HashMap<Name, &'ctx [NodeId]>>,
}


impl<'ast, 'ctx> Scoreboard<'ast, 'ctx> {
	/// Create a new empty scoreboard.
	pub fn new(arenas: &'ctx Arenas) -> Scoreboard<'ast, 'ctx> {
		Scoreboard {
			arenas: arenas,
			root_id: NodeId::new(0),
			next_id: 1,
			vhdl: vhdl::score::Scoreboard::new(&arenas.vhdl),
			libs: HashMap::new(),
			// asts: HashMap::new(),
			// hirs: HashMap::new(),
			// defs: HashMap::new(),
		}
	}

	/// Allocate a new unused node ID.
	pub fn alloc_id(&mut self) -> NodeId {
		let id = NodeId::new(self.next_id);
		self.next_id += 1;
		id
	}

	/// Add a library to the scoreboard.
	pub fn add_library(&mut self, name: Name, asts: &'ast [Ast]) -> LibRef {
		let id = LibRef::new(self.alloc_id());
		self.libs.insert(id, asts);
		// self.defs
		// 	.entry(self.root_id)
		// 	.or_insert_with(|| HashMap::new())
		// 	.insert(name, self.arenas.id.alloc_extend(vec![id].into_iter()));
		id
	}
}


impl<'ast, 'ctx> moore_common::score::Scoreboard for Scoreboard<'ast, 'ctx> {

}


impl<'ast, 'ctx> std::fmt::Debug for Scoreboard<'ast, 'ctx> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "Next ID: {}", self.next_id)?;
		write!(f, "\nLibraries:")?;
		for (k,v) in &self.libs {
			write!(f, "\n - {}: contains {} root nodes", k, v.len())?;
		}
		Ok(())
	}
}


/// A collection of arenas that the scoreboard uses to allocate nodes in. This
/// also contains the sub-arenas for the VHDL- and SystemVerilog-specific
/// scoreboards.
pub struct Arenas {
	vhdl: vhdl::score::Arenas,
}


impl Arenas {
	/// Create a new collection of arenas for the scoreboard to use.
	pub fn new() -> Arenas {
		Arenas {
			vhdl: vhdl::score::Arenas::new(),
		}
	}
}


/// Roots for every AST that we support. During parsing, a list of these entries
/// is generated that is then passed to the `Scoreboard` as a reference.
#[derive(Debug)]
pub enum Ast {
	Vhdl(Vec<vhdl_ast::DesignUnit>),
	Svlog(svlog_ast::Root),
}


// Declare some node references.
node_ref!(LibRef);
