// Copyright (c) 2017-2018 Fabian Schuiki

//! A compiler pass that gathers definitions.

#[deny(missing_docs)]

use std::collections::HashMap;
use moore_common::source::*;
use moore_common::errors::*;
use moore_common::score::Result;
use score::*;
use syntax::ast;

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

	/// Declare a primary name in the scope.
	///
	/// This converts the name to a `ResolvableName` and calls `declare()`.
	pub fn declare_primary_name(&mut self, name: &ast::PrimaryName, def: Def) {
		match self.ctx.resolvable_from_primary_name(name) {
			Ok(n) => self.declare(n, def),
			Err(()) => self.failed = true,
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
		use syntax::ast;
		let ast = self.ctx.ast(id).1;
		self.declare(ast.name.map_into(), Def::Type(id));
		// This is a rather hacky way of declaring the variant names for enum
		// literals, but it does not require the HIR to be constructed, which is
		// a requirement to avoid infinite loops.
		match ast.data {
			Some(Spanned{ value: ast::EnumType(ref paren_elems), .. }) => {
				for (i, lit) in paren_elems.value.iter().enumerate() {
					match lit.expr.data {
						ast::NameExpr(ref name) => self.declare(
							match self.ctx.resolvable_from_primary_name(&name.primary) {
								Ok(n) => n,
								Err(()) => continue
							},
							Def::Enum(EnumRef(id, i))
						),
						_ => ()
					}
				}
			}
			_ => ()
		}
	}

	/// Handle subtype declarations.
	pub fn declare_subtype(&mut self, id: SubtypeDeclRef) {
		self.declare(self.ctx.ast(id).1.name.map_into(), Def::Subtype(id))
	}

	/// Handle any of the declarations that can appear in a block.
	pub fn declare_any_in_block(&mut self, id: DeclInBlockRef) {
		match id {
			DeclInBlockRef::Subprog(id)      => self.declare_subprog(id),
			DeclInBlockRef::SubprogInst(id)  => self.declare_subprog_inst(id),
			DeclInBlockRef::SubprogBody(_id) => (),
			DeclInBlockRef::Pkg(id)          => self.declare_pkg(id),
			DeclInBlockRef::PkgInst(id)      => self.declare_pkg_inst(id),
			DeclInBlockRef::PkgBody(_id)     => (),
			DeclInBlockRef::Type(id)         => self.declare_type(id),
			DeclInBlockRef::Subtype(id)      => self.declare_subtype(id),
			DeclInBlockRef::Const(id)        => self.declare_const(id),
			DeclInBlockRef::Signal(id)       => self.declare_signal(id),
			DeclInBlockRef::SharedVar(id)    => self.declare_shared_var(id),
			DeclInBlockRef::File(id)         => self.declare_file(id),
		}
	}

	/// Handle any of the declarations that can appear in a package.
	pub fn declare_any_in_pkg(&mut self, id: DeclInPkgRef) {
		match id {
			DeclInPkgRef::Subprog(id)     => self.declare_subprog(id),
			DeclInPkgRef::SubprogInst(id) => self.declare_subprog_inst(id),
			DeclInPkgRef::Pkg(id)         => self.declare_pkg(id),
			DeclInPkgRef::PkgInst(id)     => self.declare_pkg_inst(id),
			DeclInPkgRef::Type(id)        => self.declare_type(id),
			DeclInPkgRef::Subtype(id)     => self.declare_subtype(id),
			DeclInPkgRef::Const(id)       => self.declare_const(id),
			DeclInPkgRef::Signal(id)      => self.declare_signal(id),
			DeclInPkgRef::Var(id)         => self.declare_var(id),
			DeclInPkgRef::File(id)        => self.declare_file(id),
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

	/// Handle subprogram declarations.
	pub fn declare_subprog(&mut self, id: SubprogDeclRef) {
		self.declare_primary_name(&self.ctx.ast(id).1.spec.name, Def::Subprog(id))
	}

	/// Handle subprogram instantiations.
	pub fn declare_subprog_inst(&mut self, id: SubprogInstRef) {
		self.declare_primary_name(&self.ctx.ast(id).1.spec.name, Def::SubprogInst(id))
	}
}
