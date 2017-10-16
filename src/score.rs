// Copyright (c) 2017 Fabian Schuiki
#![allow(dead_code)]

//! This module implements the scoreboard. The scoreboard is where the compiler
//! keeps track of intermediate results and processed artifacts, and where
//! additional compilation steps are initiated. This enables on-demand
//! compilation.

use std;
use std::collections::HashMap;
use typed_arena::Arena;
use moore_common;
use moore_common::Session;
use moore_common::name::Name;
use moore_common::errors::*;
use moore_common::NodeId;
use moore_common::score::NodeMaker;
use moore_vhdl::syntax::ast as vhdl_ast;
use moore_vhdl as vhdl;
use moore_svlog::ast as svlog_ast;


pub type Result<T> = std::result::Result<T, ()>;


/// The global scoreboard that drives the compilation of pretty much anything.
pub struct Scoreboard<'ast, 'ctx> {
	/// The compiler session which carries the options and is used to emit
	/// diagnostics.
	sess: &'ctx Session,
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
	libs: HashMap<LibRef, (Name, &'ast [Ast])>,
	/// A table of definitions in each scope.
	defs: HashMap<ScopeRef, &'ctx Scope>,
	// /// A table of unprocessed AST nodes.
	// asts: HashMap<NodeId, Ast<'ast>>,
	// /// A table of processed HIR nodes.
	// hirs: HashMap<NodeId, &'ctx Hir>,
}


impl<'ast, 'ctx> Scoreboard<'ast, 'ctx> {
	/// Create a new empty scoreboard.
	pub fn new(sess: &'ctx Session, arenas: &'ctx Arenas) -> Scoreboard<'ast, 'ctx> {
		Scoreboard {
			sess: sess,
			arenas: arenas,
			root_id: NodeId::new(0),
			next_id: 1,
			vhdl: vhdl::score::Scoreboard::new(&arenas.vhdl),
			libs: HashMap::new(),
			defs: HashMap::new(),
			// asts: HashMap::new(),
			// hirs: HashMap::new(),
		}
	}

	/// Emit a diagnostic message.
	pub fn emit(&self, err: DiagBuilder2) {
		println!("{}", err);
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
		self.libs.insert(id, (name, asts));
		// if self.defs
		// 	.borrow()
		// 	.entry(self.root_id)
		// 	.or_insert_with(|| HashMap::new())
		// 	.insert(name, Def::Lib(id))
		// 	.is_some() {
		// 	panic!("library {} already defined", name);
		// }
		id
	}

	pub fn defs(&mut self, id: ScopeRef) -> Result<&'ctx Scope> {
		if let Some(&s) = self.defs.get(&id) {
			Ok(s)
		} else {
			let s = self.make(id)?;
			if self.defs.insert(id, s).is_some() {
				panic!("node should not exist");
			}
			Ok(s)
		}
	}
}


impl<'ast, 'ctx> moore_common::score::Scoreboard for Scoreboard<'ast, 'ctx> {

}


impl<'ast, 'ctx> std::fmt::Debug for Scoreboard<'ast, 'ctx> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "Next ID: {}", self.next_id)?;
		write!(f, "\nLibraries:")?;
		for (k,v) in &self.libs {
			write!(f, "\n - {}: contains {} root nodes", k, v.1.len())?;
		}
		write!(f, "\nDefs:")?;
		for (k,&v) in &self.defs {
			write!(f, "\n - scope {:?}: contains {} defs nodes", k, v.len())?;
			for (n,d) in v {
				write!(f, "\n   - `{}` -> {:?}", n, d)?;
			}
		}
		Ok(())
	}
}


impl<'ast, 'ctx> NodeMaker<'ctx, ScopeRef, Scope> for Scoreboard<'ast, 'ctx> {
	fn make(&mut self, id: ScopeRef) -> Result<&'ctx Scope> {
		println!("trying to make scope {:?}", id);
		match id {
			ScopeRef::Root(_) => {
				// Gather the names of all libraries and create a root scope out
				// of them.
				let mut scope = HashMap::new();
				for (&id, &(name, _)) in &self.libs {
					if scope.insert(name, Def::Lib(id)).is_some() {
						self.sess.emit(DiagBuilder2::fatal("Library `{}` defined multiple times"));
						return Err(());
					}
				}
				Ok(self.arenas.scope.alloc(scope))
			}

			ScopeRef::Lib(id) => {
				unimplemented!("defs for lib");
			}
		}
	}
}


/// A collection of arenas that the scoreboard uses to allocate nodes in. This
/// also contains the sub-arenas for the VHDL- and SystemVerilog-specific
/// scoreboards.
pub struct Arenas {
	vhdl: vhdl::score::Arenas,
	scope: Arena<Scope>,
}


impl Arenas {
	/// Create a new collection of arenas for the scoreboard to use.
	pub fn new() -> Arenas {
		Arenas {
			vhdl: vhdl::score::Arenas::new(),
			scope: Arena::new(),
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


/// A scope, i.e. a map of names and definitions.
type Scope = HashMap<Name, Def>;


// Declare some node references.
node_ref!(RootRef);
node_ref!(LibRef);

// Declare some node reference groups.
node_ref_group!(Def: Lib(LibRef));
node_ref_group!(ScopeRef: Root(RootRef), Lib(LibRef));
