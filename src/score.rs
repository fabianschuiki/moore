// Copyright (c) 2017 Fabian Schuiki
#![allow(dead_code)]

//! This module implements the scoreboard. The scoreboard is where the compiler
//! keeps track of intermediate results and processed artifacts, and where
//! additional compilation steps are initiated. This enables on-demand
//! compilation.

use std;
use std::collections::{HashMap, HashSet};
use std::cell::RefCell;
use typed_arena::Arena;
use moore_common;
use moore_common::Session;
use moore_common::name::Name;
use moore_common::errors::*;
use moore_common::NodeId;
use moore_common::score::{NodeMaker, Result};
use moore_vhdl::syntax::ast as vhdl_ast;
use moore_vhdl as vhdl;
use moore_svlog::ast as svlog_ast;


/// The global scoreboard that drives the compilation of pretty much anything.
pub struct Scoreboard<'ast, 'ctx> {
	/// The compiler session which carries the options and is used to emit
	/// diagnostics.
	sess: &'ctx Session,
	/// The arenas within which the various nodes will be allocated.
	arenas: &'ctx Arenas,
	/// The root node ID, where the libraries live.
	pub root: RootRef,
	/// The VHDL scoreboard.
	vhdl: vhdl::score::Scoreboard<'ast, 'ctx>,
	/// A table of library nodes. This is the only node that is actively
	/// maintained by the global scoreboard.
	libs: HashMap<LibRef, (Name, &'ast [Ast])>,
	/// A table of definitions in each scope.
	defs: RefCell<HashMap<ScopeRef, &'ctx Scope>>,
}


impl<'ast, 'ctx> Scoreboard<'ast, 'ctx> {
	/// Create a new empty scoreboard.
	pub fn new(sess: &'ctx Session, arenas: &'ctx Arenas) -> Scoreboard<'ast, 'ctx> {
		Scoreboard {
			sess: sess,
			arenas: arenas,
			root: RootRef::new(NodeId::alloc()),
			vhdl: vhdl::score::Scoreboard::new(sess, &arenas.vhdl),
			libs: HashMap::new(),
			defs: RefCell::new(HashMap::new()),
		}
	}

	/// Emit a diagnostic message.
	pub fn emit(&self, err: DiagBuilder2) {
		println!("{}", err);
	}

	/// Add a library to the scoreboard.
	pub fn add_library(&mut self, name: Name, asts: &'ast [Ast]) -> LibRef {
		let id = LibRef::new(NodeId::alloc());
		self.libs.insert(id, (name, asts));

		// Pass on the VHDL nodes to the VHDL scoreboard.
		let vhdl_ast = asts
			.iter()
			.flat_map(|v| match *v {
				Ast::Vhdl(ref a) => a.iter(),
				_ => [].iter()
			})
			.collect();
		self.vhdl.add_library(vhdl::score::LibRef::new(id.into()), vhdl_ast);

		// TODO: Do the same for the SVLOG scoreboard.
		id
	}

	pub fn defs(&self, id: ScopeRef) -> Result<&'ctx Scope> {
		if let Some(&node) = self.defs.borrow().get(&id) {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB] make scope for {:?}", id); }
		let node = self.make(id)?;
		if self.sess.opts.trace_scoreboard { println!("[SB] scope for {:?} is {:?}", id, node); }
		if self.defs.borrow_mut().insert(id, node).is_some() {
			panic!("node should not exist");
		}
		Ok(node)
	}
}


impl<'ast, 'ctx> moore_common::score::Scoreboard for Scoreboard<'ast, 'ctx> {

}


impl<'ast, 'ctx> std::fmt::Debug for Scoreboard<'ast, 'ctx> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "\nLibraries:")?;
		for (k,v) in &self.libs {
			write!(f, "\n - {}: contains {} root nodes", k, v.1.len())?;
		}
		write!(f, "\nDefs:")?;
		for (k,&v) in self.defs.borrow().iter() {
			write!(f, "\n - scope {:?}: contains {} defs nodes", k, v.len())?;
			for (n,d) in v {
				write!(f, "\n   - `{}` -> {:?}", n, d)?;
			}
		}
		Ok(())
	}
}


impl<'ast, 'ctx> NodeMaker<ScopeRef, &'ctx Scope> for Scoreboard<'ast, 'ctx> {
	fn make(&self, id: ScopeRef) -> Result<&'ctx Scope> {
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
				let lib = self.libs[&id];
				// Approach:
				// 1) ask vhdl scoreboard for the defs
				// 2) ask svlog scoreboard for the defs
				// 3) create new def that is the union of the two and return

				// Ask the VHDL scoreboard for the definitions in this library.
				let vhdl = self.vhdl.defs(vhdl::score::ScopeRef::Lib(vhdl::score::LibRef::new(id.into())))?;
				if self.sess.opts.trace_scoreboard { println!("[SB] vhdl_sb returned {:?}", vhdl); }

				// Build a union of the names defined by the above scoreboards.
				// Then determine the actual definition for each name, and throw
				// an error if multiple definitions are encountered.
				let names: HashSet<Name> = vhdl.iter().map(|(&k,_)| k).collect();
				let mut defs = HashMap::new();
				let mut had_dups = false;
				for name in names {
					let both_spans: Vec<_> = vhdl[&name].iter().map(|v| v.span).collect(); // TODO: chain with svlog results
					if both_spans.len() > 1 {
						let mut d = DiagBuilder2::error(format!("`{}` declared multiple times", name));
						for span in both_spans {
							d = d.span(span);
						}
						self.sess.emit(d);
						had_dups = true;
						continue;
					}
					let mut both_defs = vhdl[&name].iter().map(|v| Def::Vhdl(v.value)); // TODO: chain with svlog results
					defs.insert(name, both_defs.nth(0).unwrap());
				}
				if had_dups {
					return Err(());
				}

				// Return the scope of definitions.
				Ok(self.arenas.scope.alloc(defs))
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
pub type Scope = HashMap<Name, Def>;


// Declare some node references.
node_ref!(RootRef);
node_ref!(LibRef);

// Declare some node reference groups.
node_ref_group!(Def:
	Lib(LibRef),
	Vhdl(vhdl::score::Def),
);
node_ref_group!(ScopeRef: Root(RootRef), Lib(LibRef),);
