// Copyright (c) 2017 Fabian Schuiki
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_variables)]
#![allow(dead_code)]

//! This module implements the renumbering pass for the VHDL AST. This pass
//! allocates node IDs, builds a hierarchy of scopes, and adds a definition to
//! them for every item in the tree that can be referred to by name.

use std;
use moore_common::source::*;
use moore_common::errors::*;
use syntax::ast::{self, NodeId, def_name_from_primary_name};
use symtbl::{SymTbl, Scope, Def, DefName};


type Result<T> = std::result::Result<T, ()>;


pub struct Lowerer<'ts> {
	pub symtbl: &'ts mut SymTbl,
	severity: Severity,
	scope_stack: Vec<NodeId>,
}

impl<'ts> Lowerer<'ts> {
	/// Create a new renumberer.
	pub fn new(symtbl: &'ts mut SymTbl) -> Lowerer<'ts> {
		Lowerer {
			symtbl: symtbl,
			severity: Severity::Note,
			scope_stack: Vec::new(),
		}
	}

	pub fn push_scope(&mut self, scope_id: NodeId) {
		assert!(self.symtbl.scopes.contains_key(&scope_id));
		self.scope_stack.push(scope_id);
	}

	pub fn pop_scope(&mut self) {
		self.scope_stack.pop().expect("scope stack was empty");
	}

	pub fn current_scope(&self) -> NodeId {
		*self.scope_stack.last().expect("scope stack was empty")
	}

	fn emit(&mut self, diag: DiagBuilder2) {
		use std::cmp::max;
		self.severity = max(self.severity, diag.get_severity());
		// TODO: Actually propagate this diagnostic to a proper location!
		println!("{}", diag);
	}


	/// Resolve a name within the given scope context. Return a vector of
	/// definitions upon success, or an error if nothing matched the name. A
	/// diagnostic is emitted in the latter case.
	pub fn resolve(&mut self, name: Spanned<DefName>, scope_id: NodeId) -> Result<Vec<(Span, Def)>> {
		// println!("resolving {}", name.value);
		let mut scope_id = Some(scope_id);
		while let Some(id) = scope_id {
			let scope = match self.symtbl.scopes.get(&id) {
				Some(s) => s,
				None => {
					panic!("{}",
						DiagBuilder2::fatal(format!("Scope ID {} does not exist", id))
						.span(name.span)
					);
				}
			};
			if let Some(defs) = scope.defs.get(&name.value) {
				return Ok(defs.clone());
			}
			scope_id = scope.parent_id;
		}

		// If we arrive here, nothing matching the name was found. Emit a
		// diagnostic message.
		self.emit(
			DiagBuilder2::error(format!("Cannot find name `{}` in this scope", name.value))
			.span(name.span)
		);
		return Err(());
	}

	/// Partially resolve a compound name. The resolution stops either if all
	/// parts of the name have been resolved, or when a part is encountered that
	/// cannot be resolved.
	fn resolve_compound_name(&mut self, node: ast::CompoundName) -> Result<(ResolName, Vec<ast::NamePart>)> {
		// Resolve the primary name.
		let mut def_name = def_name_from_primary_name(&node.primary);
		let mut defs = {
			let current = self.current_scope();
			self.resolve(def_name, current)?
		};

		// Resolve the primary names as far as possible. After the loop ends,
		// collect the remaining parts that have not been resolved into a
		// vector.
		let mut parts = node.parts.into_iter();
		loop {
			// If the last round selected multiple definitions, simply return
			// them and let the caller handle potential ambiguities.
			assert_eq!(defs.is_empty(), false);
			if defs.len() > 1 {
				return Ok((ResolName::Many(defs, def_name.value), parts.collect()));
			}

			// If the last round selected one single definition, and that
			// definition was something which we can traverse into and select
			// more definitions, look at the next part in the name and perform
			// the lookup.
			let def = defs[0];
			match def.1 {
				Def::Lib(id) |
				Def::Pkg(id) |
				Def::PkgInst(id) => {
					match parts.next() {
						Some(ast::NamePart::Select(name)) => {
							def_name = def_name_from_primary_name(&name);
							defs = self.resolve(def_name, id)?;
						}
						Some(ast::NamePart::SelectAll(name)) => {
							return Ok((ResolName::All(id), parts.collect()));
						}
						_ => {
							// No parts are left, or the parts that are left
							// should be handled by the caller.
							return Ok((ResolName::One(def.0, def.1, def_name.value), parts.collect()));
						}
					}
				}
				_ => {
					// The definition that was selected in the last round does
					// not allow for trivial name lookup, so we just return the
					// definition and let the caller decide.
					return Ok((ResolName::One(def.0, def.1, def_name.value), parts.collect()));
				}
			}
		}
	}


	pub fn fold_design_unit(&mut self, mut node: ast::DesignUnit) {
		self.push_scope(node.id);
		for n in node.ctx {
			match self.fold_ctx_item(n) {
				Ok(_) => (),
				Err(_) => (),
			};
		}
		self.pop_scope();
	}

	pub fn fold_ctx_item(&mut self, node: ast::CtxItem) -> Result<()> {
		match node {
			ast::CtxItem::LibClause(names) => {
				// println!("library {:?}", names);
			}
			ast::CtxItem::UseClause(names) => {
				// println!("use {:?}", names);
				for name in names.value {
					let res = self.resolve_compound_name(name)?;
					println!("use: {:?}", res);
					// let def_name = def_name_from_primary_name(&name.primary);
					// let root_def = {
					// 	let s = self.current_scope();
					// 	self.resolve(def_name, s)?
					// };
					// println!("use: `{:?}` resolves to {:?}", name.primary.kind, root_def);

					// // Reduce the list of definitions to the library ID.
					// let lib_id = {
					// 	if root_def.len() > 1 {
					// 		self.emit(
					// 			DiagBuilder2::error(format!("name `{}` is ambiguous; {} definitions match the name", def_name.value, root_def.len()))
					// 			.span(def_name.span)
					// 		);
					// 		return Err(());
					// 	}
					// 	match root_def[0].1 {
					// 		Def::Lib(id) => id,
					// 		_ => {
					// 			self.emit(
					// 				DiagBuilder2::error(format!("name `{}` does not refer to a library", def_name.value))
					// 				.span(def_name.span)
					// 			);
					// 			return Err(());
					// 		}
					// 	}
					// };
					// println!("use: `{:?}` resolves to {:?}", name.primary.kind, lib_id);

					// // Resolve each part of the name individually.
					// let mut scope_id = lib_id;
					// for part in &name.parts {
					// 	println!("  `{:?}` resolves to ???", part);
					// }
				}
			}
			ast::CtxItem::CtxRef(names) => {
				// println!("context ref {:?}", names);
				// TODO: Interpret the items in the context within the current
				// scope.
			}
		}
		Ok(())
	}
}


#[derive(Debug)]
enum ResolName {
	One(Span, Def, DefName),
	Many(Vec<(Span, Def)>, DefName),
	All(NodeId),
}
