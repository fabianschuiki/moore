// Copyright (c) 2017-2018 Fabian Schuiki

//! A compiler pass that gathers definitions.

#[deny(missing_docs)]

use std::collections::HashMap;
use moore_common::source::*;
use moore_common::errors::*;
use moore_common::score::Result;
use score::*;
use syntax::ast;
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
			DeclInBlockRef::Alias(id)        => self.declare_alias(id),
			DeclInBlockRef::Comp(id)         => self.declare_comp(id),
			DeclInBlockRef::Attr(id)         => self.declare_attr(id),
			DeclInBlockRef::AttrSpec(_id)    => (),
			DeclInBlockRef::CfgSpec(_id)     => (),
			DeclInBlockRef::Discon(_id)      => (),
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
			DeclInPkgRef::Alias(id)       => self.declare_alias(id),
			DeclInPkgRef::Comp(id)        => self.declare_comp(id),
			DeclInPkgRef::Attr(id)        => self.declare_attr(id),
			DeclInPkgRef::AttrSpec(_id)   => (),
			DeclInPkgRef::Discon(_id)     => (),
		}
	}

	/// Handle any of the declarations that can appear in a package.
	pub fn declare_any_in_pkg_body(&mut self, id: DeclInPkgBodyRef) {
		match id {
			DeclInPkgBodyRef::Subprog(id)      => self.declare_subprog(id),
			DeclInPkgBodyRef::SubprogBody(_id) => (),
			DeclInPkgBodyRef::SubprogInst(id)  => self.declare_subprog_inst(id),
			DeclInPkgBodyRef::Pkg(id)          => self.declare_pkg(id),
			DeclInPkgBodyRef::PkgBody(_id)     => (),
			DeclInPkgBodyRef::PkgInst(id)      => self.declare_pkg_inst(id),
			DeclInPkgBodyRef::Type(id)         => self.declare_type(id),
			DeclInPkgBodyRef::Subtype(id)      => self.declare_subtype(id),
			DeclInPkgBodyRef::Const(id)        => self.declare_const(id),
			DeclInPkgBodyRef::Var(id)          => self.declare_var(id),
			DeclInPkgBodyRef::File(id)         => self.declare_file(id),
			DeclInPkgBodyRef::Alias(id)        => self.declare_alias(id),
			DeclInPkgBodyRef::Attr(id)         => self.declare_attr(id),
			DeclInPkgBodyRef::AttrSpec(_id)    => (),
		}
	}

	/// Handle any of the declarations that can appear in a subprogram.
	pub fn declare_any_in_subprog(&mut self, id: DeclInSubprogRef) {
		match id {
			DeclInSubprogRef::Subprog(id)      => self.declare_subprog(id),
			DeclInSubprogRef::SubprogBody(_id) => (),
			DeclInSubprogRef::SubprogInst(id)  => self.declare_subprog_inst(id),
			DeclInSubprogRef::Pkg(id)          => self.declare_pkg(id),
			DeclInSubprogRef::PkgBody(_id)     => (),
			DeclInSubprogRef::PkgInst(id)      => self.declare_pkg_inst(id),
			DeclInSubprogRef::Type(id)         => self.declare_type(id),
			DeclInSubprogRef::Subtype(id)      => self.declare_subtype(id),
			DeclInSubprogRef::Const(id)        => self.declare_const(id),
			DeclInSubprogRef::Var(id)          => self.declare_var(id),
			DeclInSubprogRef::File(id)         => self.declare_file(id),
			DeclInSubprogRef::Alias(id)        => self.declare_alias(id),
			DeclInSubprogRef::Attr(id)         => self.declare_attr(id),
			DeclInSubprogRef::AttrSpec(_id)    => (),
		}
	}

	/// Handle a constant declaration.
	pub fn declare_const(&mut self, id: ConstDeclRef) {
		let hir = match self.ctx.existing_hir(id) {
			Ok(h) => h,
			Err(()) => { self.failed = true; return; }
		};
		self.declare(hir.name.map_into(), Def::Const(id.into()))
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
	pub fn declare_var(&mut self, id: VarDeclRef) {
		let hir = match self.ctx.existing_hir(id) {
			Ok(h) => h,
			Err(()) => { self.failed = true; return; }
		};
		self.declare(hir.name.map_into(), Def::Var(id.into()))
	}

	/// Handle a shared variable declaration.
	pub fn declare_shared_var(&mut self, id: SharedVarDeclRef) {
		let hir = match self.ctx.existing_hir(id) {
			Ok(h) => h,
			Err(()) => { self.failed = true; return; }
		};
		self.declare(hir.name.map_into(), Def::SharedVar(id.into()))
	}

	/// Handle a file declaration.
	pub fn declare_file(&mut self, id: FileDeclRef) {
		let hir = match self.ctx.existing_hir(id) {
			Ok(h) => h,
			Err(()) => { self.failed = true; return; }
		};
		self.declare(hir.name.map_into(), Def::File(id.into()))
	}

	/// Handle an alias declaration.
	pub fn declare_alias(&mut self, id: AliasDeclRef) {
		self.declare_primary_name(&self.ctx.ast(id).1.name, Def::Alias(id))
	}

	/// Handle a component declaration.
	pub fn declare_comp(&mut self, id: CompDeclRef) {
		self.declare(self.ctx.ast(id).1.name.map_into(), Def::Comp(id))
	}

	/// Handle an attribute declaration.
	pub fn declare_attr(&mut self, id: AttrDeclRef) {
		self.declare(self.ctx.ast(id).1.name.map_into(), Def::Attr(id))
	}

	/// Handle subprogram declarations.
	pub fn declare_subprog(&mut self, id: SubprogDeclRef) {
		self.declare_primary_name(&self.ctx.ast(id).1.spec.name, Def::Subprog(id))
	}

	/// Handle subprogram instantiations.
	pub fn declare_subprog_inst(&mut self, id: SubprogInstRef) {
		self.declare_primary_name(&self.ctx.ast(id).1.spec.name, Def::SubprogInst(id))
	}

	/// Handle subprogram specifications.
	///
	/// Note that this does not declare the subprogram itself, but rather its
	/// parameters and generics.
	pub fn declare_subprog_spec(&mut self, hir: &hir::SubprogSpec) {
		self.declare_generics(&hir.generics);
		self.declare_intf_objs(&hir.params);
	}

	/// Handle interface objects.
	///
	/// These are mainly subprogram parameters and entity ports.
	pub fn declare_intf_objs(&mut self, ids: &[IntfObjRef]) {
		if !ids.is_empty() {
			unimplemented!();
		}
	}

	/// Handle generics.
	pub fn declare_generics(&mut self, ids: &[GenericRef]) {
		if !ids.is_empty() {
			unimplemented!();
		}
	}
}
