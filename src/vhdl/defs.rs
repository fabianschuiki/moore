// Copyright (c) 2017-2018 Fabian Schuiki

//! A compiler pass that gathers definitions.

#[deny(missing_docs)]

use std::collections::HashMap;
use moore_common::source::*;
use moore_common::errors::*;
use moore_common::score::Result;
use score::*;
use hir;

/// A context to declare things in.
///
/// This context helps gather the definitions in a scope. It accepts definitions
/// and keeps track of errors that occurred. Once done the context can be
/// converted into the actual definitions, which fails in case of errors.
pub struct DefsContext<'sbc, 'sb: 'sbc, 'ast: 'sb, 'ctx: 'sb> {
	/// The parent context.
	ctx: &'sbc ScoreContext<'sb, 'ast, 'ctx>,
	/// The definitions made.
	defs: Defs,
	/// Whether any of the declarations caused an error.
	failed: bool,
}

impl<'sbc, 'sb, 'ast, 'ctx> DefsContext<'sbc, 'sb, 'ast, 'ctx> {
	/// Create a new definition context.
	pub fn new(ctx: &'sbc ScoreContext<'sb, 'ast, 'ctx>) -> DefsContext<'sbc, 'sb, 'ast, 'ctx> {
		DefsContext {
			ctx: ctx,
			defs: HashMap::new(),
			failed: false,
		}
	}

	/// Consume the context and return the definitions that were made.
	///
	/// Returns an error if an error occurred during the earlier gathering of
	/// definitions.
	pub fn finish(self) -> Result<Defs> {
		if self.failed {
			Err(())
		} else {
			Ok(self.defs)
		}
	}

	/// Emit a diagnostic message.
	pub fn emit(&mut self, diag: DiagBuilder2) {
		if diag.severity >= Severity::Error {
			self.failed = true;
		}
		self.ctx.sess.emit(diag)
	}

	/// Declare a name in the scope.
	pub fn declare(&mut self, name: Spanned<ResolvableName>, def: Def) {
		if self.ctx.sess.opts.trace_scoreboard { println!("[SB][VHDL][SCOPE] declaring `{}` as {:?}", name.value, def); }
		match def {
			// Handle overloadable cases.
			Def::Enum(_) => {
				self.defs
					.entry(name.value)
					.or_insert_with(|| Vec::new())
					.push(Spanned::new(def, name.span));
			},

			// Handle unique cases.
			_ => {
				let ins = self.defs.insert(name.value, vec![Spanned::new(def, name.span)]);
				if let Some(existing) = ins {
					self.emit(
						DiagBuilder2::error(format!("`{}` has already been declared", name.value))
						.span(name.span)
						.add_note("previous declaration was here:")
						.span(existing.last().unwrap().span)
					);
				}
			}
		}
	}

	/// Handle package declarations.
	pub fn declare_pkg(&mut self, id: PkgDeclRef) {
		self.declare(self.ctx.ast(id).1.name.map_into(), Def::Pkg(id))
	}

	/// Handle package instantiations.
	pub fn declare_pkg_inst(&mut self, id: PkgInstRef) {
		self.declare(self.ctx.ast(id).1.name.map_into(), Def::PkgInst(id))
	}

	/// Handle type declarations.
	pub fn declare_type(&mut self, id: TypeDeclRef) {
		let hir = match self.ctx.hir(id) {
			Ok(h) => h,
			Err(()) => { self.failed = true; return; }
		};
		self.declare(hir.name.map_into(), Def::Type(id));
		hir.data.as_ref().map(|data| match data.value {
			hir::TypeData::Enum(ref lits) => {
				for (i, lit) in lits.iter().enumerate() {
					match *lit {
						hir::EnumLit::Ident(n) => self.declare(n.map_into(), Def::Enum(EnumRef(id, i))),
						hir::EnumLit::Char(c)  => self.declare(c.map_into(), Def::Enum(EnumRef(id, i))),
					}
				}
			}
			hir::TypeData::Range(..) => (),
			hir::TypeData::Access(..) => (),
			hir::TypeData::Array(..) => (),
		});
	}

	/// Handle subtype declarations.
	pub fn declare_subtype(&mut self, id: SubtypeDeclRef) {
		self.declare(self.ctx.ast(id).1.name.map_into(), Def::Subtype(id))
	}

	/// Handle any of the declarations that can appear in a block.
	pub fn declare_any_in_block(&mut self, id: DeclInBlockRef) {
		match id {
			DeclInBlockRef::Pkg(id)       => self.declare_pkg(id),
			DeclInBlockRef::PkgInst(id)   => self.declare_pkg_inst(id),
			DeclInBlockRef::Type(id)      => self.declare_type(id),
			DeclInBlockRef::Subtype(id)   => self.declare_subtype(id),
			DeclInBlockRef::Const(id)     => self.declare_const(id),
			DeclInBlockRef::Signal(id)    => self.declare_signal(id),
			DeclInBlockRef::SharedVar(id) => self.declare_shared_var(id),
			DeclInBlockRef::File(id)      => self.declare_file(id),
		}
	}

	/// Handle any of the declarations that can appear in a package.
	pub fn declare_any_in_pkg(&mut self, id: DeclInPkgRef) {
		match id {
			DeclInPkgRef::Pkg(id)     => self.declare_pkg(id),
			DeclInPkgRef::PkgInst(id) => self.declare_pkg_inst(id),
			DeclInPkgRef::Type(id)    => self.declare_type(id),
			DeclInPkgRef::Subtype(id) => self.declare_subtype(id),
		}
	}

	/// Handle a constant declaration.
	pub fn declare_const(&mut self, _id: ConstDeclRef) {
		unimplemented!();
		// self.declare(self.ctx.ast(id).1.name.map_into(), Def::Const(id))
	}

	/// Handle a signal declaration.
	pub fn declare_signal(&mut self, id: SignalDeclRef) {
		let hir = match self.ctx.existing_hir(id) {
			Ok(h) => h,
			Err(()) => { self.failed = true; return; }
		};
		self.declare(hir.name.map_into(), Def::Signal(id.into()))
	}

	/// Handle a variable declaration.
	pub fn declare_var(&mut self, _id: VarDeclRef) {
		unimplemented!();
		// self.declare(self.ctx.ast(id).1.name.map_into(), Def::Const(id))
	}

	/// Handle a shared variable declaration.
	pub fn declare_shared_var(&mut self, _id: SharedVarDeclRef) {
		unimplemented!();
		// self.declare(self.ctx.ast(id).1.name.map_into(), Def::Const(id))
	}

	/// Handle a file declaration.
	pub fn declare_file(&mut self, _id: FileDeclRef) {
		unimplemented!();
		// self.declare(self.ctx.ast(id).1.name.map_into(), Def::Const(id))
	}
}
