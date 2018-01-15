// Copyright (c) 2017 Fabian Schuiki

//! This module implements lowering of the AST to the HIR.
//!
//! Note that unpacking here refers to the process of taking a reference to an
//! AST node, creating an ID for it, and adding it to the AST table for later
//! lowering to HIR.

use score::*;

/// Emit a compiler bug and return `Err`.
macro_rules! unimp {
	($slf:tt, $id:expr) => {{
		$slf.sess.emit(DiagBuilder2::bug(format!("lowering to HIR of {:?} not implemented", $id)));
		return Err(());
	}}
}

impl<'sb, 'ast, 'ctx> ScoreContext<'sb, 'ast, 'ctx> {
	/// Unpack an AST expression.
	pub fn unpack_expr(&self, ast: &'ast ast::Expr, scope_id: ScopeRef) -> Result<ExprRef> {
		let id = ExprRef::new(NodeId::alloc());
		self.set_ast(id, (scope_id, ast));
		Ok(id)
	}

	/// Unpack an AST subtype indication.
	pub fn unpack_subtype_ind(&self, ast: &'ast ast::SubtypeInd, scope_id: ScopeRef) -> Result<SubtypeIndRef> {
		let id = SubtypeIndRef::new(NodeId::alloc());
		self.set_ast(id, (scope_id, ast));
		Ok(id)
	}

	/// Unpack an AST signal declaration into individual HIR signal
	/// declarations, one for each name.
	pub fn unpack_signal_decl<I>(&self, ast: &'ast ast::ObjDecl, scope_id: ScopeRef, refs: &mut Vec<I>) -> Result<()>
	where
		I: From<SignalDeclRef>
	{
		assert_eq!(ast.kind, ast::ObjKind::Signal);

		// Unpack the subtype indication.
		let ty = SubtypeIndRef::new(NodeId::alloc());
		self.set_ast(ty, (scope_id, &ast.subtype));

		// Unpack the signal kind.
		let kind = match ast.detail {
			Some(Spanned{value: ast::ObjDetail::Register, ..}) => hir::SignalKind::Register,
			Some(Spanned{value: ast::ObjDetail::Bus, ..}) => hir::SignalKind::Bus,
			Some(Spanned{span, ..}) => {
				self.sess.emit(
					DiagBuilder2::error("expected `:=` or `;`")
					.span(span)
				);
				hir::SignalKind::Normal
			}
			None => hir::SignalKind::Normal,
		};

		// Unpack the expression indicating the initial value.
		let init = if let Some(ref expr) = ast.init {
			let id = ExprRef::new(NodeId::alloc());
			self.set_ast(id, (scope_id, expr));
			self.set_type_context(id, TypeCtx::TypeOf(ty.into()));
			Some(id)
		} else {
			None
		};

		// Create a new SignalDecl for each name.
		for &name in &ast.names {
			let id = SignalDeclRef::new(NodeId::alloc());
			let hir = self.sb.arenas.hir.signal_decl.alloc(hir::SignalDecl{
				parent: scope_id,
				name: name.into(),
				subty: ty,
				kind: kind,
				init: init,
			});
			self.set_hir(id, hir);
			refs.push(id.into());
		}

		Ok(())
	}

	/// Unpack a slice of AST declarative items into a list of items admissible
	/// in the declarative part of a block.
	///
	/// See IEEE 1076-2008 section 3.3.2.
	pub fn unpack_block_decls(&self, scope_id: ScopeRef, decls: &'ast [ast::DeclItem], container_name: &str) -> Result<Vec<DeclInBlockRef>> {
		let mut refs = Vec::new();
		let mut had_fails = false;

		for decl in decls {
			match *decl {
				ast::DeclItem::PkgDecl(ref decl) => {
					let subid = PkgDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::PkgInst(ref decl) => {
					let subid = PkgInstRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::TypeDecl(ref decl) => {
					let subid = TypeDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::SubtypeDecl(ref decl) => {
					let subid = SubtypeDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::ObjDecl(ref decl) => {
					match decl.kind {
						ast::ObjKind::Const => {
							let subid = ConstDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::ObjKind::Signal => self.unpack_signal_decl(decl, scope_id, &mut refs)?,
						ast::ObjKind::Var => {
							self.sess.emit(
								DiagBuilder2::error(format!("not a shared variable; only shared variables may appear in {}", container_name))
								.span(decl.human_span())
							);
							had_fails = true;
						}
						ast::ObjKind::SharedVar => {
							let subid = SharedVarDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::ObjKind::File => {
							let subid = FileDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
					}
				}
				ref wrong => {
					self.sess.emit(
						DiagBuilder2::error(format!("a {} cannot appear in {}", wrong.desc(), container_name))
						.span(decl.human_span())
					);
					had_fails = true;
				}
			}
		}

		if had_fails {
			Err(())
		} else {
			Ok(refs)
		}
	}

	/// Unpack a slice of concurrent statements.
	///
	/// See IEEE 1076-2008 section 11.1.
	pub fn unpack_concurrent_stmts(
		&self,
		scope_id: ScopeRef,
		stmts: &'ast [ast::Stmt],
		container_name: &str
	) -> Result<Vec<ConcStmtRef>> {
		let mut refs = Vec::new();
		let mut had_fails = false;
		let unimp = |s: &ast::Stmt| self.sess.emit(
			DiagBuilder2::bug(format!("{} not implemented", s.desc()))
			.span(s.human_span())
		);
		for stmt in stmts {
			match stmt.data {
				ast::BlockStmt{..} => { unimp(stmt); had_fails = true; }
				ast::InstOrCallStmt{..} => { unimp(stmt); had_fails = true; }
				ast::AssertStmt{..} => { unimp(stmt); had_fails = true; }
				ast::AssignStmt{..} => { unimp(stmt); had_fails = true; }
				ast::SelectAssignStmt{..} => { unimp(stmt); had_fails = true; }
				ast::IfGenStmt{..} => { unimp(stmt); had_fails = true; }
				ast::CaseGenStmt{..} => { unimp(stmt); had_fails = true; }
				ast::ForGenStmt{..} => { unimp(stmt); had_fails = true; }

				ast::ProcStmt{..} => {
					let id = ProcessStmtRef(NodeId::alloc());
					self.set_ast(id, (scope_id, stmt));
					refs.push(id.into());
				}

				ref wrong => {
					self.sess.emit(
						DiagBuilder2::error(format!("a {} cannot appear in {}", wrong.desc(), container_name))
						.span(stmt.human_span())
						.add_note(format!("Only concurrent statements are allowed in {}. See IEEE 1076-2008 section 11.1.", container_name))
					);
					had_fails = true;
				}
			}
		}
		if had_fails {
			Err(())
		} else {
			Ok(refs)
		}
	}

	/// Unpack a slice of sequential statements.
	///
	/// See IEEE 1076-2008 section 10.
	pub fn unpack_sequential_stmts(
		&self,
		scope_id: ScopeRef,
		stmts: &'ast [ast::Stmt],
		container_name: &str
	) -> Result<Vec<SeqStmtRef>> {
		let mut refs = Vec::new();
		let mut had_fails = false;
		let unimp = |s: &ast::Stmt| self.sess.emit(
			DiagBuilder2::bug(format!("{} not implemented", s.desc()))
			.span(s.human_span())
		);
		for stmt in stmts {
			match stmt.data {
				ast::WaitStmt{..} => { unimp(stmt); had_fails = true; }
				ast::AssertStmt{..} => { unimp(stmt); had_fails = true; }
				ast::ReportStmt{..} => { unimp(stmt); had_fails = true; }
				ast::AssignStmt{kind: ast::AssignKind::Signal,..} => {
					let id = SigAssignStmtRef(NodeId::alloc());
					self.set_ast(id, (scope_id, stmt));
					refs.push(id.into());
				}
				ast::AssignStmt{kind: ast::AssignKind::Var, ..} => {
					let id = VarAssignStmtRef(NodeId::alloc());
					self.set_ast(id, (scope_id, stmt));
					refs.push(id.into());
				}
				ast::SelectAssignStmt{..} => { unimp(stmt); had_fails = true; }
				ast::InstOrCallStmt{..} => { unimp(stmt); had_fails = true; }
				ast::IfStmt{..} => { unimp(stmt); had_fails = true; }
				ast::CaseStmt{..} => { unimp(stmt); had_fails = true; }
				ast::LoopStmt{..} => { unimp(stmt); had_fails = true; }
				ast::NexitStmt{..} => { unimp(stmt); had_fails = true; }
				ast::ReturnStmt{..} => { unimp(stmt); had_fails = true; }

				ast::NullStmt => (),
				ref wrong => {
					self.sess.emit(
						DiagBuilder2::error(format!("a {} cannot appear in {}", wrong.desc(), container_name))
						.span(stmt.human_span())
						.add_note(format!("Only sequential statements are allowed in {}. See IEEE 1076-2008 section 10.", container_name))
					);
					had_fails = true;
				}
			}
		}
		if had_fails {
			Err(())
		} else {
			Ok(refs)
		}
	}

	/// Unpack a signal assignment target.
	///
	/// See IEEE 1076-2008 section 10.5.2.1.
	pub fn unpack_signal_assign_target(
		&self,
		scope_id: ScopeRef,
		target: &'ast ast::AssignTarget
	) -> Result<hir::SigAssignTarget> {
		match *target {
			ast::AssignTarget::Name(ref name) => {
				println!("will now resolve {:#?}", name);
				let (_res_name, mut defs, res_span, tail) = self.resolve_compound_name(name, scope_id, false)?;
				if !tail.is_empty() {
					self.sess.emit(
						DiagBuilder2::bug("handling of non-name signal assignment targets not implemented")
						.span(name.span)
					);
					return Err(());
				}
				let sig = match defs.pop() {
					Some(Spanned{ value: Def::Signal(id), .. }) => id,
					Some(_) => {
						self.sess.emit(
							DiagBuilder2::error(format!("`{}` is not a signal", res_span.extract()))
							.span(res_span)
						);
						return Err(());
					}
					None => unreachable!()
				};
				if !defs.is_empty() {
					self.sess.emit(
						DiagBuilder2::error(format!("`{}` is ambiguous", res_span.extract()))
						.span(res_span)
					);
					return Err(());
				}
				Ok(hir::SigAssignTarget::Name(sig))
			},
			ast::AssignTarget::Aggregate(ref elems) => {
				self.sess.emit(
					DiagBuilder2::error("aggregate signal assignment not implemented")
					.span(elems.span)
				);
				Err(())
			}
		}
	}

	/// Unpack a signal assignment mode.
	///
	/// See IEEE 1076-2008 section 10.5.
	pub fn unpack_signal_assign_mode(
		&self,
		scope_id: ScopeRef,
		mode: &'ast ast::AssignMode
	) -> Result<hir::SigAssignKind> {
		unimp!(self, "signal assignment mode");
	}
}


// Lower an entity to HIR.
impl_make!(self, id: EntityRef => &hir::Entity {
	let (lib, ctx_id, ast) = self.ast(id);
	let mut entity = hir::Entity{
		ctx_items: ctx_id,
		lib: lib,
		name: ast.name,
		generics: Vec::new(),
		ports: Vec::new(),
	};
	let mut port_spans = Vec::new();
	let mut generic_spans = Vec::new();
	for decl in &ast.decls {
		match *decl {
			// Port clauses
			ast::DeclItem::PortgenClause(_, Spanned{ value: ast::PortgenKind::Port, span }, ref decls) => {
				// For ports only signal interface declarations are allowed.
				port_spans.push(span);
				for decl in &decls.value {
					match *decl {
						ast::IntfDecl::ObjDecl(ref decl @ ast::IntfObjDecl{ kind: ast::IntfObjKind::Signal, .. }) => {
							let ty = SubtypeIndRef(NodeId::alloc());
							self.set_ast(ty, (id.into(), &decl.ty));
							for name in &decl.names {
								let subid = IntfSignalRef(NodeId::alloc());
								self.set_ast(subid, (id.into(), decl, ty, name));
								entity.ports.push(subid);
							}
						}
						ref wrong => {
							self.sess.emit(
								DiagBuilder2::error(format!("a {} cannot appear in a port clause", wrong.desc()))
								.span(wrong.human_span())
							);
							continue;
						}
					}
				}
			}

			// Generic clauses
			ast::DeclItem::PortgenClause(_, Spanned{ value: ast::PortgenKind::Generic, span }, ref decls) => {
				// For generics only constant, type, subprogram, and package
				// interface declarations are allowed.
				generic_spans.push(span);
				for decl in &decls.value {
					match *decl {
						ast::IntfDecl::TypeDecl(ref decl) => {
							let subid = IntfTypeRef(NodeId::alloc());
							self.set_ast(subid, (id.into(), decl));
							entity.generics.push(subid.into());
						}
						ast::IntfDecl::SubprogSpec(ref decl) => {
							let subid = IntfSubprogRef(NodeId::alloc());
							self.set_ast(subid, (id.into(), decl));
							entity.generics.push(subid.into());
						}
						ast::IntfDecl::PkgInst(ref decl) => {
							let subid = IntfPkgRef(NodeId::alloc());
							self.set_ast(subid, (id.into(), decl));
							entity.generics.push(subid.into());
						}
						ast::IntfDecl::ObjDecl(ref decl @ ast::IntfObjDecl{ kind: ast::IntfObjKind::Const, .. }) => {
							let ty = SubtypeIndRef(NodeId::alloc());
							self.set_ast(ty, (id.into(), &decl.ty));
							for name in &decl.names {
								let subid = IntfConstRef(NodeId::alloc());
								self.set_ast(subid, (id.into(), decl, ty, name));
								entity.generics.push(subid.into());
							}
						}
						ref wrong => {
							self.sess.emit(
								DiagBuilder2::error(format!("a {} cannot appear in a generic clause", wrong.desc()))
								.span(wrong.human_span())
							);
							continue;
						}
					}
				}
			}

			ref wrong => {
				self.sess.emit(
					DiagBuilder2::error(format!("a {} cannot appear in an entity declaration", wrong.desc()))
					.span(decl.human_span())
				);
				continue;
			}
		}
	}
	// TODO(strict): Complain about multiple port and generic clauses.
	// TODO(strict): Complain when port and generic clauses are not the
	// first in the entity.
	Ok(self.sb.arenas.hir.entity.alloc(entity))
});


// Lower an interface signal to HIR.
impl_make!(self, id: IntfSignalRef => &hir::IntfSignal {
	let (scope_id, decl, subty_id, ident) = self.ast(id);
	let init = match decl.default {
		Some(ref e) => {
			let subid = ExprRef(NodeId::alloc());
			self.set_ast(subid, (scope_id, e));
			Some(subid)
		}
		None => None
	};
	let sig = hir::IntfSignal {
		name: Spanned::new(ident.name, ident.span),
		mode: match decl.mode {
			None | Some(ast::IntfMode::In) => hir::IntfSignalMode::In,
			Some(ast::IntfMode::Out) => hir::IntfSignalMode::Out,
			Some(ast::IntfMode::Inout) => hir::IntfSignalMode::Inout,
			Some(ast::IntfMode::Buffer) => hir::IntfSignalMode::Buffer,
			Some(ast::IntfMode::Linkage) => hir::IntfSignalMode::Linkage,
		},
		ty: subty_id,
		bus: decl.bus,
		init: init,
	};
	Ok(self.sb.arenas.hir.intf_sig.alloc(sig))
});


// Lower a package declaration to HIR.
impl_make!(self, id: PkgDeclRef => &hir::Package {
	let (scope_id, ast) = self.ast(id);
	let generics = Vec::new();
	// let generic_maps = Vec::new();
	let mut decls = Vec::new();
	let mut had_fails = false;

	// Filter the declarations in the package to only those that we actually
	// support, and separate the generic clauses and maps.
	for decl in &ast.decls {
		match *decl {
			ast::DeclItem::PkgDecl(ref decl) => {
				let subid = PkgDeclRef(NodeId::alloc());
				self.set_ast(subid, (id.into(), decl));
				decls.push(subid.into());
			}
			ast::DeclItem::PkgInst(ref decl) => {
				let subid = PkgInstRef(NodeId::alloc());
				self.set_ast(subid, (id.into(), decl));
				decls.push(subid.into());
			}
			ast::DeclItem::TypeDecl(ref decl) => {
				let subid = TypeDeclRef(NodeId::alloc());
				self.set_ast(subid, (id.into(), decl));
				decls.push(subid.into());
			}
			ast::DeclItem::SubtypeDecl(ref decl) => {
				let subid = SubtypeDeclRef(NodeId::alloc());
				self.set_ast(subid, (id.into(), decl));
				decls.push(subid.into());
			}

			// Emit an error for any other kinds of declarations.
			ref wrong => {
				self.sess.emit(
					DiagBuilder2::error(format!("a {} cannot appear in a package declaration", wrong.desc()))
					.span(decl.human_span())
				);
				had_fails = true;
				continue;
			}
		}
	}

	if had_fails {
		Err(())
	} else {
		Ok(self.sb.arenas.hir.package.alloc(hir::Package{
			parent: scope_id,
			name: ast.name,
			generics: generics,
			decls: decls,
		}))
	}
});


// Lower a subtype indication to HIR.
impl_make!(self, id: SubtypeIndRef => &hir::SubtypeInd {
	let (scope_id, ast) = self.ast(id);

	// TODO: Implement resolution indications.
	if let Some(_) = ast.res {
		self.sess.emit(
			DiagBuilder2::error("Resolution indications on subtypes not yet supported")
			.span(ast.span)
		);
	}

	// First try to resolve the name. This will yield a list of definitions
	// and the remaining parts of the name that were not resolved. The
	// latter will contain optional constraints.
	let (_, mut defs, defs_span, tail_parts) = self.resolve_compound_name(&ast.name, scope_id, false)?;

	// Make sure that the definition is unambiguous and unpack it.
	let tm = match defs.pop() {
		Some(Spanned{value: Def::Type(id), ..}) => id.into(),
		Some(Spanned{value: Def::Subtype(id), ..}) => id.into(),
		Some(_) => {
			self.sess.emit(
				DiagBuilder2::error(format!("`{}` is not a type or subtype", ast.span.extract()))
				.span(ast.span)
			);
			return Err(());
		}
		None => unreachable!()
	};
	if !defs.is_empty() {
		self.sess.emit(
			DiagBuilder2::error(format!("`{}` is ambiguous", ast.span.extract()))
			.span(ast.span)
		);
		return Err(());
	}

	// Parse the constraint.
	let constraint = match tail_parts.last() {
		Some(&ast::NamePart::Range(ref expr)) => hir::Constraint::Range(expr.span, self.unpack_expr(expr, scope_id)?),
		Some(&ast::NamePart::Call(ref elems)) => {
			// TODO: Parse array or record constraint.
			self.sess.emit(
				DiagBuilder2::error(format!("Array and record constraints on subtype indications not yet implemented"))
				.span(elems.span)
			);
			return Err(());
		}
		Some(_) => {
			self.sess.emit(
				DiagBuilder2::error(format!("`{}` is not a type or subtype", ast.span.extract()))
				.span(ast.span)
			);
			return Err(());
		}
		None => hir::Constraint::None,
	};
	if tail_parts.len() > 1 {
		self.sess.emit(
			DiagBuilder2::error(format!("`{}` is not a type or subtype", ast.span.extract()))
			.span(ast.span)
		);
		return Err(());
	}

	Ok(self.sb.arenas.hir.subtype_ind.alloc(hir::SubtypeInd{
		span: ast.span,
		type_mark: Spanned::new(tm, defs_span),
		constraint: constraint,
	}))
});


impl_make!(self, id: SubtypeDeclRef => &hir::SubtypeDecl {
	let (scope_id, ast) = self.ast(id);
	let subty = self.unpack_subtype_ind(&ast.subtype, scope_id)?;
	Ok(self.sb.arenas.hir.subtype_decl.alloc(hir::SubtypeDecl{
		parent: scope_id,
		name: ast.name,
		subty: subty,
	}))
});


// Lower an expression to HIR.
impl_make!(self, id: ExprRef => &hir::Expr {
	let (scope_id, ast) = self.ast(id);
	let data = match ast.data {
		// Literals
		ast::LitExpr(ref lit, ref _unit) => {
			use syntax::lexer::token::Literal;
			match *lit {
				Literal::Abstract(base, int, frac, exp) => {
					// Parse the base.
					let base = match base {
						Some(base) => match base.as_str().parse() {
							Ok(base) => base,
							Err(_) => {
								self.sess.emit(
									DiagBuilder2::error(format!("`{}` is not a valid base for a number literal", base))
									.span(ast.span)
								);
								return Err(());
							}
						},
						None => 10,
					};

					// Parse the rest of the number.
					if frac.is_none() && exp.is_none() {
						match BigInt::parse_bytes(int.as_str().as_bytes(), base) {
							Some(v) => hir::ExprData::IntegerLiteral(ConstInt::new(None, v)),
							None => {
								self.sess.emit(
									DiagBuilder2::error(format!("`{}` is not a valid base-{} integer", int, base))
									.span(ast.span)
								);
								return Err(());
							}
						}
					} else {
						self.sess.emit(
							DiagBuilder2::error("Float literals not yet supported")
							.span(ast.span)
						);
						return Err(());
					}
				}
				_ => {
					self.sess.emit(
						DiagBuilder2::error("Literal not yet supported")
						.span(ast.span)
					);
					return Err(());
				}
			}
		}

		// Unary operators.
		ast::UnaryExpr(op, ref arg) => {
			let op = match op {
				ast::UnaryOp::Not => hir::UnaryOp::Not,
				ast::UnaryOp::Abs => hir::UnaryOp::Abs,
				ast::UnaryOp::Sign(ast::Sign::Pos) => hir::UnaryOp::Pos,
				ast::UnaryOp::Sign(ast::Sign::Neg) => hir::UnaryOp::Neg,
				ast::UnaryOp::Logical(op) => hir::UnaryOp::Logical(op),
				_ => {
					self.sess.emit(
						DiagBuilder2::error("invalid unary operator")
						.span(ast.span)
					);
					return Err(());
				}
			};
			let subid = ExprRef(NodeId::alloc());
			self.set_ast(subid, (scope_id, arg.as_ref()));
			hir::ExprData::Unary(op, subid)
		}

		// Ranges.
		ast::BinaryExpr(ast::BinaryOp::Dir(d), ref lb, ref rb) => {
			hir::ExprData::Range(d, self.unpack_expr(lb, scope_id)?, self.unpack_expr(rb, scope_id)?)
		}

		// Binary operators.
		// ast::BinaryExpr(op, ref lhs, ref rhs) => {

		// }

		// Names.
		ast::NameExpr(ref name) => {
			let (_, defs, matched_span, tail_parts) = self.resolve_compound_name(name, scope_id, false)?;
			println!("name {} matched {:?}, tail {:?}", name.span.extract(), defs, tail_parts);

			// If there are multiple definitions, perform overload resolution by
			// consulting the type context for the expression.
			let defs: Vec<_> = if defs.len() > 1 {
				if let Some(tyctx) = self.type_context(id) {
					let ty = self.deref_named_type(match tyctx {
						TypeCtx::Type(t) => t,
						TypeCtx::TypeOf(id) => self.ty(id)?,
					})?;
					if self.sess.opts.trace_scoreboard {
						println!("[SB][VHDL][OVLD] resolve overloaded `{}`", matched_span.extract());
						println!("[SB][VHDL][OVLD] context requires {:?}", ty);
					}

					// Filter out the defs that are typed and that match the
					// type imposed by the expression context.
					let mut filtered = Vec::new();
					for def in defs {
						let defty = self.deref_named_type(match def.value {
							Def::Enum(EnumRef(id,_)) => self.ty(id)?,
							// TODO: Add subprograms and everything else that
							// can match here.
							_ => {
								if self.sess.opts.trace_scoreboard {
									println!("[SB][VHDL][OVLD] discarding irrelevant {:?}", def.value);
								}
								continue;
							}
						})?;
						if defty == ty {
							filtered.push(def);
							if self.sess.opts.trace_scoreboard {
								println!("[SB][VHDL][OVLD] accepting {:?}", def.value);
							}
						} else {
							if self.sess.opts.trace_scoreboard {
								println!("[SB][VHDL][OVLD] discarding {:?} because mismatching type {:?}", def.value, defty);
							}
						}
					}

					// If the filtering left no overloads, emit an error.
					if filtered.is_empty() {
						self.sess.emit(
							DiagBuilder2::error(format!("no overload of `{}` applicable", matched_span.extract()))
							.span(matched_span)
						);
						// TODO: Print the required type and the type of what
						// has been found.
						return Err(());
					}
					filtered
				} else {
					defs
				}
			} else {
				defs
			};

			// Make sure we only have one definition. If we have more than one,
			// perform overload resolution by consulting the type context for
			// the expression.
			let def = if defs.len() == 1 {
				*defs.last().unwrap()
			} else {
				self.sess.emit(
					DiagBuilder2::error(format!("`{}` is ambiguous", matched_span.extract()))
					.span(matched_span)
				);
				return Err(());
			};

			// Create the expression representation of the definition.
			let mut expr: &'ctx hir::Expr = self.sb.arenas.hir.expr.alloc(hir::Expr{
				parent: scope_id,
				span: matched_span,
				data: hir::ExprData::Name(def.value, def.span),
			});

			// Unpack the remaining parts of the name.
			for part in tail_parts {
				// Allocate a node ID for the inner expression and store it away in
				// the HIR table.
				let inner = ExprRef::new(NodeId::alloc());
				let inner_span = expr.span;
				self.set_hir(inner, expr);

				match *part {
					ast::NamePart::Select(name) => {
						let rn = self.resolvable_from_primary_name(&name)?;
						expr = self.sb.arenas.hir.expr.alloc(hir::Expr{
							parent: scope_id,
							span: Span::union(inner_span, rn.span),
							data: hir::ExprData::Select(inner, rn),
						});
					}

					ast::NamePart::Signature(ref _sig) => unimplemented!(),

					ast::NamePart::Attribute(ident) => {
						expr = self.sb.arenas.hir.expr.alloc(hir::Expr{
							parent: scope_id,
							span: Span::union(inner_span, ident.span),
							data: hir::ExprData::Attr(inner, Spanned::new(ident.name.into(), ident.span)),
						});
					}

					// Call expressions can map to different things. First we need
					// to know what type the callee has. Based on this, the list of
					// arguments can be associated with the correct ports. Or in
					// case the callee is a type, we perform a type conversion.
					ast::NamePart::Call(ref _elems) => {
						let callee_ty = self.ty(inner)?;
						panic!("call to {:?} not implemented", callee_ty);
						// let mut had_named = false;
						// for i in 0..elems.len() {

						// }
					}

					// Disallow `.all` in expressions.
					ast::NamePart::SelectAll(span) => {
						self.sess.emit(
							DiagBuilder2::error("`.all` in an expression")
							.span(span)
						);
						return Err(());
					}

					// Disallow ranges in expressions.
					ast::NamePart::Range(ref expr) => {
						self.sess.emit(
							DiagBuilder2::error("range in an expression")
							.span(expr.span)
						);
						return Err(());
					}
				}
			}

			// return self.compound_name_to_expr(name, scope_id);
			return Ok(expr);
		}

		// All other expressions we simply do not support.
		_ => {
			self.sess.emit(
				DiagBuilder2::error("invalid expression")
				.span(ast.span)
			);
			return Err(());
		}
	};
	Ok(self.sb.arenas.hir.expr.alloc(hir::Expr{
		parent: scope_id,
		span: ast.span,
		data: data,
	}))
});


// Lower a type declaration to HIR.
impl_make!(self, id: TypeDeclRef => &hir::TypeDecl {
	let (scope_id, ast) = self.ast(id);
	let data = match ast.data {
		// Integer, real, and physical types.
		Some(ast::RangeType(_span, ref range_expr, ref _units)) => {
			let (dir, lb, rb) = match range_expr.data {
				ast::BinaryExpr(ast::BinaryOp::Dir(dir), ref lb_expr, ref rb_expr) => {
					let lb = ExprRef(NodeId::alloc());
					let rb = ExprRef(NodeId::alloc());
					self.set_ast(lb, (scope_id.into(), lb_expr.as_ref()));
					self.set_ast(rb, (scope_id.into(), rb_expr.as_ref()));
					(dir, lb, rb)
				}
				_ => {
					self.sess.emit(
						DiagBuilder2::error("Invalid range expression")
						.span(range_expr.span)
					);
					return Err(());
				}
			};
			// TODO: Handle units
			Some(hir::TypeData::Range(range_expr.span, dir, lb, rb))
		}

		// Enumeration types.
		Some(ast::EnumType(ref elems)) => {
			let mut lits = Vec::new();
			for elem in &elems.value {
				// Unpack the element. Make sure it only consists of an
				// expression that is either an identifier or a character
				// literal.
				let lit = if !elem.choices.is_empty() {
					None
				} else {
					match elem.expr.data {
						ast::NameExpr(ast::CompoundName{
							primary: ast::PrimaryName{ kind, span, .. },
							ref parts,
							..
						}) if parts.is_empty() => {
							match kind {
								ast::PrimaryNameKind::Ident(n) => Some(hir::EnumLit::Ident(Spanned::new(n, span))),
								ast::PrimaryNameKind::Char(c) => Some(hir::EnumLit::Char(Spanned::new(c, span))),
								_ => None,
							}
						}
						_ => None
					}
				};

				// If the unpacking was successful, add the literal to the list
				// of enumeration literals.
				if let Some(lit) = lit {
					println!("got enum literal {:?}", lit);
					lits.push(lit);
				} else {
					self.sess.emit(
						DiagBuilder2::error("not an enumeration literal")
						.span(elem.span)
						.add_note("expected identifier or character literal")
					);
					continue;
				}
			}
			Some(hir::TypeData::Enum(elems.span, lits))
		}

		Some(ref wrong) => {
			self.sess.emit(
				DiagBuilder2::bug(format!("lowering to HIR of {} not implemented", wrong.desc()))
				.span(wrong.human_span())
			);
			return Err(());
		},
		None => None
	};
	let decl = hir::TypeDecl{
		parent: scope_id,
		name: ast.name,
		data: data,
	};
	Ok(self.sb.arenas.hir.type_decl.alloc(decl))
});

// Lower an architecture to HIR.
impl_make!(self, id: ArchRef => &hir::Arch {
	let (lib_id, ctx_id, ast) = self.ast(id);
	let decls = self.unpack_block_decls(id.into(), &ast.decls, "an architecture")?;
	let stmts = self.unpack_concurrent_stmts(id.into(), &ast.stmts, "an architecture")?;
	let entity_id = *self.archs(lib_id)?.by_arch.get(&id).unwrap();
	Ok(self.sb.arenas.hir.arch.alloc(hir::Arch{
		ctx_items: ctx_id,
		entity: entity_id,
		name: ast.name,
		decls: decls,
		stmts: stmts,
	}))
});

impl_make!(self, id: ProcessStmtRef => &hir::ProcessStmt {
	let (scope_id, ast) = self.ast(id);
	match ast.data {
		ast::ProcStmt {
			// ref sensitivity,
			// ref decls,
			ref stmts,
			postponed,
			..
		} => {
			// TODO: map sensititivty
			// TODO: map decls
			let stmts = self.unpack_sequential_stmts(id.into(), stmts, "a process")?;
			Ok(self.sb.arenas.hir.process_stmt.alloc(hir::ProcessStmt {
				parent: scope_id,
				label: ast.label,
				postponed: postponed,
				sensitivity: hir::ProcessSensitivity::None,
				decls: Vec::new(),
				stmts: stmts,
			}))
		}
		_ => unreachable!()
	}
});

impl_make!(self, id: SigAssignStmtRef => &hir::SigAssignStmt {
	let (scope_id, ast) = self.ast(id);
	match ast.data {
		ast::AssignStmt {
			target: Spanned{ value: ref target, span: target_span },
			mode: Spanned{ value: ref mode, span: mode_span },
			guarded,
			..
		} => {
			let target = self.unpack_signal_assign_target(scope_id, target)?;
			let kind = self.unpack_signal_assign_mode(scope_id, mode)?;
			if guarded {
				self.sess.emit(
					DiagBuilder2::warning("sequential signal assignment cannot be guarded")
					.span(ast.human_span())
					.add_note("Only concurrent signal assignments can be guarded. See IEEE 1076-2008 section 11.6.")
				);
			}
			Ok(self.sb.arenas.hir.sig_assign_stmt.alloc(hir::SigAssignStmt {
				parent: scope_id,
				span: ast.span,
				label: ast.label,
				target: target,
				target_span: target_span,
				kind: kind,
				kind_span: mode_span,
			}))
		}
		_ => unreachable!()
	}
});

// ast::AssignStmt {
// 	ref target,
// 	kind: ast::AssignKind::Signal,
// 	guarded,
// 	ref mode,
// } => {
// 	let id = SigAssignStmtRef(NodeId::alloc());
// 	let target = self.unpack_signal_assign_target(scope_id, target)?;
// 	let kind = self.unpack_signal_assign_mode(scope_id, mode)?;
// 	if guarded {
// 		self.sess.emit(
// 			DiagBuilder2::warning("sequential signal assignment cannot be guarded")
// 			.span(stmt.human_span())
// 			.add_note("Only concurrent signal assignments can be guarded. See IEEE 1076-2008 section 11.6.")
// 		);
// 	}
// 	let assign = hir::SigAssignStmt {
// 		parent: scope_id,
// 		label: stmt.label,
// 		target: target,
// 		kind: kind,
// 	};
// 	self.set_hir(id, self.sb.arenas.hir.sig_assign_stmt.alloc(assign));
// 	refs.push(id.into());
// }

// ast::AssignStmt {
// 	ref target,
// 	kind: ast::AssignKind::Var,
// 	guarded,
// 	ref mode,
// } => {
// 	unimp(stmt);
// 	had_fails = true;
// }

