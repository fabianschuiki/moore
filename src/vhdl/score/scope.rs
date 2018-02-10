// Copyright (c) 2017 Fabian Schuiki

//! This module implements the tracking of definitions and scopes for VHDL.

use score::*;
use defs::*;


macro_rules! impl_make_defs {
	($slf:tt, $id:ident: $id_ty:ty => $blk:block) => {
		impl_make!($slf, $id: $id_ty => &Defs $blk);
	}
}

macro_rules! impl_make_scope {
	($slf:tt, $id:ident: $id_ty:ty => $blk:block) => {
		impl_make!($slf, $id: $id_ty => &Scope $blk);
	}
}


impl_make_defs!(self, id: ScopeRef => {
	match id {
		ScopeRef::Lib(id)         => self.make(id),
		ScopeRef::CtxItems(id)    => self.make(id),
		ScopeRef::Entity(id)      => self.make(id),
		ScopeRef::BuiltinPkg(id)  => Ok(&(*BUILTIN_PKG_DEFS)[&id]),
		ScopeRef::Pkg(id)         => self.make(id),
		ScopeRef::PkgBody(id)     => self.make(id),
		ScopeRef::Arch(id)        => self.make(id),
		ScopeRef::Process(id)     => self.make(id),
		ScopeRef::Subprog(id)     => self.make(id),
		ScopeRef::SubprogBody(id) => self.make(id),
	}
});

impl_make_scope!(self, id: ScopeRef => {
	match id {
		ScopeRef::Lib(id)         => self.make(id),
		ScopeRef::CtxItems(_)     => unreachable!(),
		ScopeRef::Entity(id)      => self.make(id),
		ScopeRef::BuiltinPkg(id)  => Ok(&(*BUILTIN_PKG_SCOPES)[&id]),
		ScopeRef::Pkg(id)         => self.make(id),
		ScopeRef::PkgBody(id)     => self.make(id),
		ScopeRef::Arch(id)        => self.make(id),
		ScopeRef::Process(id)     => self.make(id),
		ScopeRef::Subprog(id)     => self.make(id),
		ScopeRef::SubprogBody(id) => self.make(id),
	}
});


// Definitions in a library.
impl_make_defs!(self, id: LibRef => {
	// Approach:
	// 1) Get the HIR of the library
	// 2) Gather definitions from the HIR.
	// 3) Create defs and return.
	let lib = self.hir(id)?;

	// Assemble an uber-iterator that will iterate over each
	// definition in the library. We do this by obtaining an
	// iterator for every design unit type in the library, then
	// mapping each ID to the corresponding name and definition.
	// The name is determined by looking up the AST node of the
	// design unit to be defined.
	let iter = lib.entities.iter().map(|&n| (self.ast(n).2.name, Def::Entity(n)));
	let iter = iter.chain(lib.cfgs.iter().map(|&n| (self.ast(n).2.name, Def::Cfg(n))));
	let iter = iter.chain(lib.pkg_decls.iter().map(|&n| (self.ast(n).1.name, Def::Pkg(n))));
	let iter = iter.chain(lib.pkg_insts.iter().map(|&n| (self.ast(n).1.name, Def::PkgInst(n))));
	let iter = iter.chain(lib.ctxs.iter().map(|&n| (self.ast(n).2.name, Def::Ctx(n))));

	// For every element the iterator produces, add it to the map of
	// definitions.
	let mut defs = HashMap::new();
	for (name, def) in iter {
		defs.entry(name.value.into()).or_insert_with(|| Vec::new()).push(Spanned::new(def, name.span));
	}

	// Warn the user about duplicate definitions.
	let mut had_dups = false;
	for (name, defs) in &defs {
		if defs.len() <= 1 {
			continue;
		}
		let mut d = DiagBuilder2::error(format!("`{}` declared multiple times", name));
		for def in defs {
			d = d.span(def.span);
		}
		self.emit(d);
		had_dups = true;
	}
	if had_dups {
		return Err(());
	}

	// Return the definitions.
	Ok(self.sb.arenas.defs.alloc(defs))
});


// Definitions made by the context items that appear before design units.
impl_make_defs!(self, id: CtxItemsRef => {
	let (_, ast) = self.ast(id);
	let mut defs = HashMap::new();
	let mut has_fails = false;
	for item in ast {
		// For each name in a library clause, find the corresponding library
		// and create a definition for it.
		match *item {
			ast::CtxItem::LibClause(Spanned{ value: ref names, .. }) => {
				for ident in names {
					if let Some(&lib_id) = self.sb.lib_names.borrow().get(&ident.name) {
						let defs = defs.entry(ident.name.into()).or_insert_with(||vec![]);
						if !defs.is_empty() {
							self.emit(
								DiagBuilder2::error(format!("`{}` has already been declared", ident.name))
								.span(ident.span)
								// TODO: Show previous declarations
							);
							has_fails = true;
						} else {
							defs.push(Spanned::new(Def::Lib(lib_id), ident.span));
						}
					} else {
						self.emit(
							DiagBuilder2::error(format!("no library named `{}` found", ident.name))
							.span(ident.span)
							// TODO: Print list of libraries.
						);
						has_fails = true;
					}
				}
			}
			_ => ()
		}
	}
	if has_fails {
		Err(())
	} else {
		Ok(self.sb.arenas.defs.alloc(defs))
	}
});


// Definitions in an entity.
impl_make_defs!(self, _id: EntityRef => {
	// TODO: Implement this.
	Ok(self.sb.arenas.defs.alloc(HashMap::new()))
});


// Definitions in an architecture.
impl_make_defs!(self, id: ArchRef => {
	let mut ctx = DefsContext::new(self);
	let hir = self.hir(id)?;
	for &decl in &hir.decls {
		ctx.declare_any_in_block(decl);
	}
	Ok(self.sb.arenas.defs.alloc(ctx.finish()?))
});

// Definitions in a package declaration.
impl_make_defs!(self, id: PkgDeclRef => {
	let mut ctx = DefsContext::new(self);
	let hir = self.hir(id)?;
	for &decl in &hir.decls {
		ctx.declare_any_in_pkg(decl);
	}
	Ok(self.sb.arenas.defs.alloc(ctx.finish()?))
});

// Definitions in a package body.
impl_make_defs!(self, id: PkgBodyRef => {
	let mut ctx = DefsContext::new(self);
	let hir = self.hir(id)?;
	for &decl in &hir.decls {
		ctx.declare_any_in_pkg_body(decl);
	}
	Ok(self.sb.arenas.defs.alloc(ctx.finish()?))
});

// Definitions in a subprogram declaration.
impl_make_defs!(self, id: SubprogDeclRef => {
	let mut ctx = DefsContext::new(self);
	let hir = self.hir(id)?;
	ctx.declare_subprog_spec(&hir.spec);
	Ok(self.sb.arenas.defs.alloc(ctx.finish()?))
});

// Definitions in a subprogram body.
impl_make_defs!(self, id: SubprogBodyRef => {
	let mut ctx = DefsContext::new(self);
	let hir = self.hir(id)?;
	ctx.declare_subprog_spec(&hir.spec);
	for &decl in &hir.decls {
		ctx.declare_any_in_subprog(decl);
	}
	Ok(self.sb.arenas.defs.alloc(ctx.finish()?))
});


// Populate the scope of a library.
impl_make_scope!(self, id: LibRef => {
	let mut defs = Vec::new();
	defs.push(id.into());
	Ok(self.sb.arenas.scope.alloc(Scope{
		parent: None,
		defs: defs,
		explicit_defs: HashMap::new(),
	}))
});


impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
	// Populate the scope of the context items that appear before a design unit. The
	// scope of the design unit itself is a subscope of the context items.
	pub fn make_ctx_items_scope(&self, id: CtxItemsRef, parent: Option<ScopeRef>) -> Result<CtxItemsRef> {
		let (_, items) = self.ast(id);
		let mut defs = Vec::new();
		let mut explicit_defs = HashMap::new();
		defs.push(id.into());
		for item in items {
			if let &ast::CtxItem::UseClause(Spanned{value: ref names, ..}) = item {
				for name in names {
					// TODO: This creates an infinite loop, since the name lookup requires the context items to be ready.
					let (res_name, mut out_defs, valid_span, mut tail) = self.resolve_compound_name(name, id.into(), true)?;
					println!("resolving use clause {:?}", name);

					// Resolve the optional `all`.
					match tail.first() {
						Some(&ast::NamePart::SelectAll(all_span)) => {
							tail = &tail[1..];
							match out_defs.pop() {
								Some(Spanned{value: Def::Pkg(id), ..}) => {
									defs.push(id.into());
								}
								Some(_) => {
									self.emit(
										DiagBuilder2::error(format!("`all` not possible on `{}`", valid_span.extract()))
										.span(all_span)
									);
									continue;
								}
								None => unreachable!()
							}
						}
						_ => {
							explicit_defs.entry(res_name).or_insert_with(|| Vec::new()).extend(out_defs);
						}
					}
					println!("yields explicit_defs {:?}", explicit_defs);

					// Ensure that there is no garbage.
					if tail.len() > 0 {
						let span = Span::union(valid_span.end().into(), name.span.end());
						self.emit(
							DiagBuilder2::error("invalid name suffix")
							.span(span)
						);
						continue;
					}
				}
			}
		}
		self.sb.scope_table.borrow_mut().insert(id.into(), self.sb.arenas.scope.alloc(Scope{
			parent: parent,
			defs: defs,
			explicit_defs: explicit_defs,
		}));
		Ok(id)
	}
}


// Populate the scope of an entity.
impl_make_scope!(self, id: EntityRef => {
	let hir = self.hir(id)?;
	let mut defs = Vec::new();
	defs.push(id.into());
	let parent = self.make_ctx_items_scope(hir.ctx_items, None)?;
	Ok(self.sb.arenas.scope.alloc(Scope{
		parent: Some(parent.into()),
		defs: defs,
		explicit_defs: HashMap::new(),
	}))
});


// Populate the scope of an architecture.
impl_make_scope!(self, id: ArchRef => {
	let hir = self.hir(id)?;
	let mut defs = Vec::new();
	defs.push(id.into());
	let parent = self.make_ctx_items_scope(hir.ctx_items, Some(hir.entity.into()))?;
	Ok(self.sb.arenas.scope.alloc(Scope{
		parent: Some(parent.into()),
		defs: defs,
		explicit_defs: HashMap::new(),
	}))
});

// Populate the scope of a package declaration.
impl_make_scope!(self, id: PkgDeclRef => {
	let hir = self.hir(id)?;
	let mut defs = Vec::new();
	defs.push(id.into());
	let parent = match hir.parent {
		ScopeRef::CtxItems(id) => self.make_ctx_items_scope(id, None)?.into(),
		others => others
	};
	Ok(self.sb.arenas.scope.alloc(Scope{
		parent: Some(parent),
		defs: defs,
		explicit_defs: HashMap::new(),
	}))
});

// Populate the scope of a package body.
impl_make_scope!(self, id: PkgBodyRef => {
	let hir = self.hir(id)?;
	let mut defs = Vec::new();
	defs.push(id.into());
	let parent = match hir.parent {
		ScopeRef::CtxItems(id) => self.make_ctx_items_scope(id, None)?.into(),
		others => others
	};
	Ok(self.sb.arenas.scope.alloc(Scope{
		parent: Some(parent),
		defs: defs,
		explicit_defs: HashMap::new(),
	}))
});

// Populate the scope of a subprogram declaration.
impl_make_scope!(self, id: SubprogDeclRef => {
	let hir = self.hir(id)?;
	let mut defs = Vec::new();
	defs.push(id.into());
	let parent = match hir.parent {
		ScopeRef::CtxItems(id) => self.make_ctx_items_scope(id, None)?.into(),
		others => others
	};
	Ok(self.sb.arenas.scope.alloc(Scope{
		parent: Some(parent),
		defs: defs,
		explicit_defs: HashMap::new(),
	}))
});

// Populate the scope of a subprogram body.
impl_make_scope!(self, id: SubprogBodyRef => {
	let hir = self.hir(id)?;
	let mut defs = Vec::new();
	defs.push(id.into());
	let parent = match hir.parent {
		ScopeRef::CtxItems(id) => self.make_ctx_items_scope(id, None)?.into(),
		others => others
	};
	Ok(self.sb.arenas.scope.alloc(Scope{
		parent: Some(parent),
		defs: defs,
		explicit_defs: HashMap::new(),
	}))
});

impl_make_defs!(self, id: ProcessStmtRef => {
	let mut ctx = DefsContext::new(self);
	let hir = self.hir(id)?;
	for &decl in &hir.decls {
		ctx.declare_any_in_process(decl);
	}
	Ok(self.sb.arenas.defs.alloc(ctx.finish()?))
});

impl_make_scope!(self, id: ProcessStmtRef => {
	let hir = self.existing_hir(id)?;
	let mut defs = Vec::new();
	defs.push(id.into());
	Ok(self.sb.arenas.scope.alloc(Scope {
		parent: Some(hir.parent),
		defs: defs,
		explicit_defs: HashMap::new(),
	}))
});

// DeclInPkgRef::Pkg(id) => vec![(self.ast(id).1.name.map_into(), Def::Pkg(id))],
// DeclInPkgRef::PkgInst(id) => vec![(self.ast(id).1.name.map_into(), Def::PkgInst(id))],
// DeclInPkgRef::Type(id) => {
// 	let hir = self.hir(id)?;
// 	let mut v = vec![(hir.name.map_into(), Def::Type(id))];
// 	match hir.data {
// 		Some(hir::TypeData::Enum(_, ref lits)) => {
// 			for (i, lit) in lits.iter().enumerate() {
// 				match *lit {
// 					hir::EnumLit::Ident(n) => v.push((n.map_into(), Def::Enum(EnumRef(id, i)))),
// 					hir::EnumLit::Char(c) => v.push((c.map_into(), Def::Enum(EnumRef(id, i)))),
// 				}
// 			}
// 		}
// 		_ => ()
// 	}
// 	v
// }
// DeclInPkgRef::Subtype(id) => vec![(self.ast(id).1.name.map_into(), Def::Subtype(id))],
