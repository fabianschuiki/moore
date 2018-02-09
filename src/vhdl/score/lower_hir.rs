// Copyright (c) 2017 Fabian Schuiki

//! This module implements lowering of the AST to the HIR.
//!
//! Note that unpacking here refers to the process of taking a reference to an
//! AST node, creating an ID for it, and adding it to the AST table for later
//! lowering to HIR.

use score::*;
use syntax::lexer::token::Literal;

/// Emit a compiler bug and return `Err`.
macro_rules! unimp {
	($slf:tt, $id:expr) => {{
		$slf.emit(
			DiagBuilder2::bug(format!("lowering to HIR of {:?} not implemented", $id))
		);
		return Err(());
	}};
	($slf:tt, $id:expr, $span:expr) => {{
		$slf.emit(
			DiagBuilder2::bug(format!("lowering to HIR of {:?} not implemented", $id))
			.span($span)
		);
		return Err(());
	}}
}

macro_rules! unimp_msg {
	($slf:tt, $msg:expr) => {{
		$slf.emit(
			DiagBuilder2::bug(format!("lowering to HIR: {} not implemented", $msg))
		);
		return Err(());
	}};
	($slf:tt, $msg:expr, $span:expr) => {{
		$slf.emit(
			DiagBuilder2::bug(format!("lowering to HIR: {} not implemented", $msg))
			.span($span)
		);
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
		// let ctx = TermContext::new(self, scope_id);
		// let term = ctx.termify_subtype_ind(ast)?;
		// let id = ctx.term_to_subtype_ind(term)?.value;
		// Ok(id)
		let id = SubtypeIndRef::new(NodeId::alloc());
		self.set_ast(id, (scope_id, ast));
		Ok(id)
	}

	/// Unpack a compound name as a type mark.
	pub fn unpack_type_mark(&self, ast: LatentName<'ast>, scope_id: ScopeRef) -> Result<Spanned<LatentTypeMarkRef>> {
		let id = LatentTypeMarkRef::new(NodeId::alloc());
		self.set_ast(id, (scope_id, ast));
		Ok(Spanned::new(id, ast.span()))
	}

	/// Unpack a compound name as a package name.
	pub fn unpack_package_name(&self, ast: LatentName<'ast>, scope_id: ScopeRef) -> Result<Spanned<LatentPkgRef>> {
		let id = LatentPkgRef::new(NodeId::alloc());
		self.set_ast(id, (scope_id, ast));
		Ok(Spanned::new(id, ast.span()))
	}

	/// Unpack a compound name as a subprogram name.
	pub fn unpack_subprog_name(&self, ast: LatentName<'ast>, scope_id: ScopeRef) -> Result<Spanned<LatentSubprogRef>> {
		let id = LatentSubprogRef::new(NodeId::alloc());
		self.set_ast(id, (scope_id, ast));
		Ok(Spanned::new(id, ast.span()))
	}

	/// Unpack an AST signal declaration into individual HIR signal
	/// declarations, one for each name.
	pub fn unpack_signal_decl<I>(&self, ast: &'ast ast::ObjDecl, scope_id: ScopeRef, refs: &mut Vec<I>) -> Result<()>
	where
		I: From<SignalDeclRef>
	{
		assert_eq!(ast.kind, ast::ObjKind::Signal);

		// Unpack the subtype indication.
		let ty = self.unpack_subtype_ind(&ast.subtype, scope_id)?;

		// Unpack the signal kind.
		let kind = match ast.detail {
			Some(Spanned{value: ast::ObjDetail::Register, ..}) => hir::SignalKind::Register,
			Some(Spanned{value: ast::ObjDetail::Bus, ..}) => hir::SignalKind::Bus,
			Some(Spanned{span, ..}) => {
				self.emit(
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
				ast::DeclItem::SubprogDecl(ref decl) => {
					match decl.data {
						ast::SubprogData::Decl => {
							let subid = SubprogDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::SubprogData::Body{..} => {
							let subid = SubprogBodyRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::SubprogData::Inst{..} => {
							let subid = SubprogInstRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
					}
				}
				ast::DeclItem::PkgDecl(ref decl) => {
					let subid = PkgDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::PkgBody(ref decl) => {
					let subid = PkgBodyRef(NodeId::alloc());
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
							self.emit(
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
				ast::DeclItem::AliasDecl(ref decl) => {
					let subid = AliasDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::CompDecl(ref decl) => {
					let subid = CompDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::AttrDecl(ref decl) => {
					match decl.data {
						ast::AttrData::Decl(..) => {
							let subid = AttrDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::AttrData::Spec{..} => {
							let subid = AttrSpecRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
					}
				}
				ref wrong => {
					self.emit(
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

	/// Unpack a slice of AST declarative items into a list of items admissible
	/// in the declarative part of a subprogram.
	///
	/// See IEEE 1076-2008 section 4.3.
	pub fn unpack_subprog_decls(
		&self,
		scope_id: ScopeRef,
		decls: &'ast [ast::DeclItem]
	) -> Result<Vec<DeclInSubprogRef>> {
		let mut refs = Vec::new();
		let mut had_fails = false;

		for decl in decls {
			match *decl {
				ast::DeclItem::SubprogDecl(ref decl) => {
					match decl.data {
						ast::SubprogData::Decl => {
							let subid = SubprogDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::SubprogData::Body{..} => {
							let subid = SubprogBodyRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::SubprogData::Inst{..} => {
							let subid = SubprogInstRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
					}
				}
				ast::DeclItem::PkgDecl(ref decl) => {
					let subid = PkgDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::PkgBody(ref decl) => {
					let subid = PkgBodyRef(NodeId::alloc());
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
						ast::ObjKind::Signal => {
							self.emit(
								DiagBuilder2::error("a signal declaration cannot appear in a subprogram")
								.span(decl.human_span())
							);
							had_fails = true;
						}
						ast::ObjKind::SharedVar => {
							self.emit(
								DiagBuilder2::error("not a variable; shared variables may not appear in a package body")
								.span(decl.human_span())
							);
							had_fails = true;
						}
						ast::ObjKind::Var => {
							let subid = VarDeclRef(NodeId::alloc());
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
					self.emit(
						DiagBuilder2::error(format!("a {} cannot appear in a subprogram", wrong.desc()))
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
		let unimp = |s: &ast::Stmt| self.emit(
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
					self.emit(
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
		let unimp = |s: &ast::Stmt| self.emit(
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
					self.emit(
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
				let (_res_name, mut defs, res_span, tail) = self.resolve_compound_name(name, scope_id, false)?;
				if !tail.is_empty() {
					self.emit(
						DiagBuilder2::bug("handling of non-name signal assignment targets not implemented")
						.span(name.span)
					);
					return Err(());
				}
				let sig = match defs.pop() {
					Some(Spanned{ value: Def::Signal(id), .. }) => id,
					Some(_) => {
						self.emit(
							DiagBuilder2::error(format!("`{}` is not a signal", res_span.extract()))
							.span(res_span)
						);
						return Err(());
					}
					None => unreachable!()
				};
				if !defs.is_empty() {
					self.emit(
						DiagBuilder2::error(format!("`{}` is ambiguous", res_span.extract()))
						.span(res_span)
					);
					return Err(());
				}
				Ok(hir::SigAssignTarget::Name(sig))
			},
			ast::AssignTarget::Aggregate(ref elems) => {
				self.emit(
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
		mode: &'ast Spanned<ast::AssignMode>,
		tyctx: &TypeCtx<'ctx>,
	) -> Result<Spanned<hir::SigAssignKind>> {
		Ok(Spanned::new(match mode.value {
			ast::AssignMode::Release(_fm) => {
				unimp!(self, "release signal assignment mode");
			}
			ast::AssignMode::Force(_fm, ref _waves) => {
				unimp!(self, "force signal assignment mode");
			}
			ast::AssignMode::Normal(ref dm, ref waves) => {
				let dm = self.unpack_delay_mechanism(scope_id, dm)?;
				assert!(!waves.is_empty()); // guaranteed by parser
				if waves.len() > 1 || waves[0].1.is_some() {
					hir::SigAssignKind::CondWave(
						dm,
						self.unpack_cond_waveforms(scope_id, waves, tyctx)?
					)
				} else {
					hir::SigAssignKind::SimpleWave(
						dm,
						self.unpack_waveform(scope_id, &waves[0].0, tyctx)?
					)
				}
			}
		}, mode.span))
	}

	/// Unpack a delay mechanism.
	///
	/// See IEEE 1076-2008 section 10.5.2.1. If no mechanism is specified,
	/// inertial is assumed. Theoretically, the inertial transport mechanism is
	/// mapped to reject-inertial with the pulse rejection limit determined by
	/// the delay of the first element in the waveform. We don't have that
	/// information readily available at this time, so we simply map to
	/// inertial and leave the resolution of this to stages further down the
	/// pipeline.
	pub fn unpack_delay_mechanism(
		&self,
		scope_id: ScopeRef,
		dm: &'ast Option<Spanned<ast::DelayMech>>,
	) -> Result<hir::DelayMechanism> {
		if let Some(Spanned { value: ref dm, .. }) = *dm {
			Ok(match *dm {
				ast::DelayMech::Transport => hir::DelayMechanism::Transport,
				ast::DelayMech::Inertial => hir::DelayMechanism::Inertial,
				ast::DelayMech::InertialReject(ref expr) => {
					let expr = self.unpack_expr(expr, scope_id)?;
					hir::DelayMechanism::RejectInertial(expr)
				}
			})
		} else {
			Ok(hir::DelayMechanism::Inertial)
		}
	}

	/// Unpack the the waves of a simple wave assignment.
	pub fn unpack_cond_waveforms(
		&self,
		_scope_id: ScopeRef,
		waves: &'ast [ast::CondWave],
		_tyctx: &TypeCtx<'ctx>,
	) -> Result<hir::Cond<hir::Waveform>> {
		// Determine if we have a "else".
		let (_when, _other) = if waves.last().unwrap().1.is_some() {
			(&waves[..], None)
		} else {
			(&waves[..waves.len()-1], Some(&waves.last().unwrap().1))
		};
		// for w in when {

		// }
		// let o = match other {
		// 	Some(o) => Some(self.unpack_waveform(scope_id, other)?),
		// 	None => None,
		// };
		unimp!(self, "conditional waveforms");
	}

	/// Unpack a single waveform.
	///
	/// See IEEE 1076-2008 section 10.5.2.
	pub fn unpack_waveform(
		&self,
		scope_id: ScopeRef,
		wave: &'ast ast::Wave,
		tyctx: &TypeCtx<'ctx>,
	) -> Result<hir::Waveform> {
		wave.elems.iter().flat_map(|i| i.iter()).map(|&(ref value, ref after)|{
			Ok(hir::WaveElem {
				value: match value.data {
					ast::NullExpr => None,
					_ => {
						let expr = self.unpack_expr(value, scope_id)?;
						self.set_type_context(expr, tyctx.clone());
						Some(expr)
					}
				},
				after: match *after {
					Some(ref expr) => {
						let expr = self.unpack_expr(expr, scope_id)?;
						// TODO: Set the type context for the expression.
						// self.set_type_context(expr, TypeCtx::Type(/* somehow refer to builtin `time` type */));
						Some(expr)
					}
					None => None
				},
			})
		}).collect()
	}

	/// Ensure that parenthesis contain only a list of expressions.
	///
	/// This is useful since the parser generally expects parenthesized
	/// expressions of the form `(expr|expr|expr => expr, expr)` even in palces
	/// where only `(expr, expr)` would be applicable. This function takes the
	/// parenthesized expression and ensures it is of the latter form.
	pub fn sanitize_paren_elems_as_exprs(&self, elems: &'ast [ast::ParenElem], context: &str) -> Vec<&'ast ast::Expr> {
		elems.iter().map(|elem|{
			if !elem.choices.is_empty() {
				let span = Span::union(elem.choices[0].span, elem.choices.last().unwrap().span);
				self.emit(
					DiagBuilder2::error(format!("`=>` not applicable in {}", context))
					.span(span)
				);
			}
			&elem.expr
		}).collect()
	}

	/// Internalize a subtype indication.
	pub fn intern_subtype_ind(&self, hir: hir::SubtypeInd) -> SubtypeIndRef {
		let id = SubtypeIndRef::new(NodeId::alloc());
		self.set_hir(id, self.sb.arenas.hir.subtype_ind.alloc(hir));
		id
	}

	/// Lower an AST unary operator to a HIR unary operator.
	///
	/// Emits an error if the operator is not a valid unary operator.
	pub fn lower_unary_op(&self, ast: Spanned<ast::UnaryOp>) -> Result<Spanned<hir::UnaryOp>> {
		let op = match ast.value {
			ast::UnaryOp::Not => hir::UnaryOp::Not,
			ast::UnaryOp::Abs => hir::UnaryOp::Abs,
			ast::UnaryOp::Sign(ast::Sign::Pos) => hir::UnaryOp::Pos,
			ast::UnaryOp::Sign(ast::Sign::Neg) => hir::UnaryOp::Neg,
			ast::UnaryOp::Logical(op) => hir::UnaryOp::Logical(op),
			_ => {
				self.emit(
					DiagBuilder2::error("invalid unary operator")
					.span(ast.span)
				);
				return Err(());
			}
		};
		Ok(Spanned::new(op, ast.span))
	}

	/// Lower an AST binary operator to a HIR binary operator.
	///
	/// Emits an error if the operator is not a valid binary operator.
	pub fn lower_binary_op(&self, ast: Spanned<ast::BinaryOp>) -> Result<Spanned<hir::BinaryOp>> {
		let op = match ast.value {
			ast::BinaryOp::Logical(op) => hir::BinaryOp::Logical(op),
			ast::BinaryOp::Rel(op) => hir::BinaryOp::Rel(op),
			ast::BinaryOp::Match(op) => hir::BinaryOp::Match(op),
			ast::BinaryOp::Shift(op) => hir::BinaryOp::Shift(op),
			ast::BinaryOp::Add => hir::BinaryOp::Add,
			ast::BinaryOp::Sub => hir::BinaryOp::Sub,
			ast::BinaryOp::Concat => hir::BinaryOp::Concat,
			ast::BinaryOp::Mul => hir::BinaryOp::Mul,
			ast::BinaryOp::Div => hir::BinaryOp::Div,
			ast::BinaryOp::Mod => hir::BinaryOp::Mod,
			ast::BinaryOp::Rem => hir::BinaryOp::Rem,
			ast::BinaryOp::Pow => hir::BinaryOp::Pow,
			_ => {
				self.emit(
					DiagBuilder2::error("invalid binary operator")
					.span(ast.span)
				);
				return Err(());
			}
		};
		Ok(Spanned::new(op, ast.span))
	}

	/// Lower an AST subprogram specification to HIR.
	pub fn lower_subprog_spec(
		&self,
		scope_id: ScopeRef,
		ast: &'ast ast::SubprogSpec
	) -> Result<hir::SubprogSpec> {
		let name = self.resolvable_from_primary_name(&ast.name)?;
		let kind = match (ast.kind, ast.purity) {
			(ast::SubprogKind::Proc, None) => hir::SubprogKind::Proc,
			(ast::SubprogKind::Func, None) |
			(ast::SubprogKind::Func, Some(ast::SubprogPurity::Pure)) => hir::SubprogKind::PureFunc,
			(ast::SubprogKind::Func, Some(ast::SubprogPurity::Impure)) => hir::SubprogKind::ImpureFunc,
			(ast::SubprogKind::Proc, Some(_)) => {
				self.emit(
					DiagBuilder2::error(format!("Procedure `{}` cannot be pure/impure", name.value))
					.span(name.span)
				);
				hir::SubprogKind::Proc
			}
		};
		let mut generics = Vec::new();
		if let Some(ref gc) = ast.generic_clause {
			self.unpack_generics(scope_id, gc, &mut generics);
		}
		if let Some(ref gm) = ast.generic_map {
			unimp_msg!(self, "lowering of generic maps in subprogram specifications", gm.span);
		}
		let generic_map = vec![];
		if ast.params.is_some() {
			unimp_msg!(self, "lowering of parameters in subprogram specifications", name.span);
		}
		let return_type = match ast.retty {
			Some(ref name) => Some(self.unpack_type_mark(name.into(), scope_id)?),
			None => None,
		};
		if ast.kind == ast::SubprogKind::Func && ast.retty.is_none() {
			self.emit(
				DiagBuilder2::error(format!("Function `{}` has no return type", name.value))
				.span(name.span)
				.add_note("Functions require a return type. Use a procedure if you want no return type. See IEEE 1076-2008 section 4.2.1.")
			);
			return Err(());
		}
		if name.value.is_bit() {
			self.emit(
				DiagBuilder2::error(format!("`{}` is not a valid subprogram name", name.value))
				.span(name.span)
				.add_note("Operators. Use a procedure if you want no return type. See IEEE 1076-2008 section 4.2.1.")
			);
			return Err(());
		}
		if ast.kind == ast::SubprogKind::Proc && !name.value.is_ident() {
			self.emit(
				DiagBuilder2::error(format!("`{}` overload must be a function", name.value))
				.span(name.span)
				.add_note("Procedures cannot overload operators. Use a function. See IEEE 1076-2008 section 4.2.1.")
			);
			return Err(());
		}
		Ok(hir::SubprogSpec {
			name: name,
			kind: kind,
			generics: generics,
			generic_map: generic_map,
			params: vec![],
			return_type: return_type,
		})
	}

	/// Unpack generics from a list of interface declarations.
	///
	/// See IEEE 1076-2008 section 6.5.6.1.
	pub fn unpack_generics(&self, scope_id: ScopeRef, decls: &'ast [ast::IntfDecl], into: &mut Vec<GenericRef>) {
		for decl in decls {
			match *decl {
				ast::IntfDecl::TypeDecl(ref decl) => {
					let id = IntfTypeRef(NodeId::alloc());
					self.set_ast(id, (scope_id, decl));
					into.push(id.into());
				}
				ast::IntfDecl::SubprogSpec(ref decl) => {
					let id = IntfSubprogRef(NodeId::alloc());
					self.set_ast(id, (scope_id, decl));
					into.push(id.into());
				}
				ast::IntfDecl::PkgInst(ref decl) => {
					let id = IntfPkgRef(NodeId::alloc());
					self.set_ast(id, (scope_id, decl));
					into.push(id.into());
				}
				ast::IntfDecl::ObjDecl(ref decl @ ast::IntfObjDecl{ kind: ast::IntfObjKind::Const, .. }) => {
					let ty = SubtypeIndRef(NodeId::alloc());
					self.set_ast(ty, (scope_id, &decl.ty));
					for name in &decl.names {
						let id = IntfConstRef(NodeId::alloc());
						self.set_ast(id, (scope_id, decl, ty, name));
						into.push(id.into());
					}
				}
				ref wrong => {
					self.emit(
						DiagBuilder2::error(format!("a {} cannot appear in a generic clause", wrong.desc()))
						.span(wrong.human_span())
					);
				}
			}
		}
	}

	/// Unpack a generic map from a parenthesized list of elements.
	///
	/// See IEEE 1076-2008 section 6.5.7.2.
	pub fn unpack_generic_map(
		&self,
		_scope_id: ScopeRef,
		elems: &'ast ast::ParenElems
	) -> Result<Vec<()>> {
		if !elems.value.is_empty() {
			unimp_msg!(self, "generic map aspect", elems.span);
		}
		Ok(Vec::new())
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
							self.emit(
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
				generic_spans.push(span);
				self.unpack_generics(id.into(), &decls.value, &mut entity.generics);
			}

			ref wrong => {
				self.emit(
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
			ast::DeclItem::SubprogDecl(ref decl) => {
				match decl.data {
					ast::SubprogData::Decl => (),
					_ => {
						self.emit(
							DiagBuilder2::error(format!("a {} cannot appear in a package declaration", decl.desc()))
							.span(decl.human_span())
							.add_note("Only subprogram declarations can appear in a package declaration. See IEEE 1076-2008 section 4.7.")
						);
						had_fails = true;
						continue;
					}
				}
				let subid = SubprogDeclRef(NodeId::alloc());
				self.set_ast(subid, (id.into(), decl));
				decls.push(subid.into());
			}
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
			ast::DeclItem::ObjDecl(ref decl) => {
				match decl.kind {
					ast::ObjKind::Const => {
						let subid = ConstDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
					ast::ObjKind::Signal => self.unpack_signal_decl(decl, scope_id, &mut decls)?,
					ast::ObjKind::SharedVar => {
						self.emit(
							DiagBuilder2::error("not a variable; shared variables may not appear in a package declaration")
							.span(decl.human_span())
						);
						had_fails = true;
					}
					ast::ObjKind::Var => {
						let subid = VarDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
					ast::ObjKind::File => {
						let subid = FileDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
				}
			}
			ref wrong => {
				self.emit(
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

// Lower a package body to HIR.
impl_make!(self, id: PkgBodyRef => &hir::PackageBody {
	let (scope_id, ast) = self.ast(id);
	let pkg = self.unpack_package_name((&ast.name).into(), scope_id)?;
	let mut decls = Vec::new();
	let mut had_fails = false;
	for decl in &ast.decls {
		match *decl {
			ast::DeclItem::SubprogDecl(ref decl) => {
				match decl.data {
					ast::SubprogData::Decl => {
						let subid = SubprogDeclRef(NodeId::alloc());
						self.set_ast(subid, (id.into(), decl));
						decls.push(subid.into());
					}
					ast::SubprogData::Body{..} => {
						let subid = SubprogBodyRef(NodeId::alloc());
						self.set_ast(subid, (id.into(), decl));
						decls.push(subid.into());
					}
					ast::SubprogData::Inst{..} => {
						let subid = SubprogInstRef(NodeId::alloc());
						self.set_ast(subid, (id.into(), decl));
						decls.push(subid.into());
					}
				}
			}
			ast::DeclItem::PkgDecl(ref decl) => {
				let subid = PkgDeclRef(NodeId::alloc());
				self.set_ast(subid, (id.into(), decl));
				decls.push(subid.into());
			}
			ast::DeclItem::PkgBody(ref decl) => {
				let subid = PkgBodyRef(NodeId::alloc());
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
			ast::DeclItem::ObjDecl(ref decl) => {
				match decl.kind {
					ast::ObjKind::Const => {
						let subid = ConstDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
					ast::ObjKind::Signal => {
						self.emit(
							DiagBuilder2::error("a signal declaration cannot appear in a package body")
							.span(decl.human_span())
						);
						had_fails = true;
					}
					ast::ObjKind::SharedVar => {
						self.emit(
							DiagBuilder2::error("not a variable; shared variables may not appear in a package body")
							.span(decl.human_span())
						);
						had_fails = true;
					}
					ast::ObjKind::Var => {
						let subid = VarDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
					ast::ObjKind::File => {
						let subid = FileDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
				}
			}
			ref wrong => {
				self.emit(
					DiagBuilder2::error(format!("a {} cannot appear in a package body", wrong.desc()))
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
		Ok(self.sb.arenas.hir.package_body.alloc(hir::PackageBody {
			parent: scope_id,
			name: ast.name,
			pkg: pkg,
			decls: decls,
		}))
	}
});

// Lower a package instantiation to HIR.
impl_make!(self, id: PkgInstRef => &hir::PackageInst {
	let (scope_id, ast) = self.ast(id);
	let pkg = self.unpack_package_name((&ast.target).into(), scope_id)?;
	let gm = match ast.generics {
		Some(ref g) => self.unpack_generic_map(scope_id, g)?,
		None => vec![],
	};
	Ok(self.sb.arenas.hir.package_inst.alloc(hir::PackageInst {
		parent: scope_id,
		name: ast.name,
		pkg: pkg,
		generic_map: gm,
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
								self.emit(
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
								self.emit(
									DiagBuilder2::error(format!("`{}` is not a valid base-{} integer", int, base))
									.span(ast.span)
								);
								return Err(());
							}
						}
					} else {
						self.emit(
							DiagBuilder2::error("Float literals not yet supported")
							.span(ast.span)
						);
						return Err(());
					}
				}
				_ => {
					self.emit(
						DiagBuilder2::error("Literal not yet supported")
						.span(ast.span)
					);
					return Err(());
				}
			}
		}

		// Unary operators.
		ast::UnaryExpr(op, ref arg) => {
			let op = self.lower_unary_op(Spanned::new(op, ast.span))?;
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
						self.emit(
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
				self.emit(
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
						self.emit(
							DiagBuilder2::error("`.all` in an expression")
							.span(span)
						);
						return Err(());
					}

					// Disallow ranges in expressions.
					ast::NamePart::Range(ref expr) => {
						self.emit(
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
			self.emit(
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
	let data = if let Some(ref spanned_data) = ast.data {
		Some(Spanned::new(match spanned_data.value {
			// Integer, real, and physical types.
			ast::RangeType(ref range_expr, ref units) => {
				let (dir, lb, rb) = match range_expr.data {
					ast::BinaryExpr(ast::BinaryOp::Dir(dir), ref lb_expr, ref rb_expr) => {
						let lb = ExprRef(NodeId::alloc());
						let rb = ExprRef(NodeId::alloc());
						self.set_ast(lb, (scope_id.into(), lb_expr.as_ref()));
						self.set_ast(rb, (scope_id.into(), rb_expr.as_ref()));
						(dir, lb, rb)
					}
					_ => {
						self.emit(
							DiagBuilder2::error("Invalid range expression")
							.span(range_expr.span)
						);
						return Err(());
					}
				};
				// TODO: Handle units
				if let Some(ref _units) = *units {
					self.emit(
						DiagBuilder2::bug("Units not yet supported")
						.span(spanned_data.span)
					);
					return Err(());
				}
				hir::TypeData::Range(dir, lb, rb)
			}

			// Enumeration types.
			ast::EnumType(ref elems) => {
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
						lits.push(lit);
					} else {
						self.emit(
							DiagBuilder2::error("not an enumeration literal")
							.span(elem.span)
							.add_note("expected an identifier or character literal")
						);
						continue;
					}
				}
				hir::TypeData::Enum(lits)
			}

			ast::AccessType(ref subty) => {
				hir::TypeData::Access(self.unpack_subtype_ind(subty, scope_id)?)
			}

			ast::ArrayType(ref indices, ref elem_subty) => {
				// Ensure that we have at least on index, and ensure that there
				// are no stray choices (`expr|expr =>`) in the list. Then map
				// each index into its own node, unpack the element subtype, and
				// we're done.
				assert!(indices.value.len() > 0);
				let indices = self
					.sanitize_paren_elems_as_exprs(&indices.value, "an array type index")
					.into_iter()
					.map(|index|{
						let id = ArrayTypeIndexRef::new(NodeId::alloc());
						self.set_ast(id, (scope_id, index));
						id
					})
					.collect();
				let ctx = TermContext::new(self, scope_id);
				let subty = ctx.termify_subtype_ind(elem_subty)?;
				let elem_subty = ctx.term_to_subtype_ind(subty)?.map(|i| self.intern_subtype_ind(i));
				hir::TypeData::Array(indices, elem_subty.value)
			}

			ast::FileType(ref name) => {
				let ctx = TermContext::new(self, scope_id);
				let term = ctx.termify_compound_name(name)?;
				let tm = ctx.term_to_type_mark(term)?;
				hir::TypeData::File(tm.value)
			}

			ast::RecordType(ref fields) => {
				let fields = fields.iter().flat_map(|&(ref names, ref subty)|{
					let subty = self.unpack_subtype_ind(subty, scope_id);
					names.iter().map(move |name| Ok((Spanned::new(name.name, name.span), subty?)))
				}).collect::<Result<Vec<_>>>()?;
				hir::TypeData::Record(fields)
			}

			ast::ProtectedType(..) => unimp_msg!(self, "protected types", ast.span),
		}, spanned_data.span))
	} else {
		None
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
			ref mode,
			guarded,
			..
		} => {
			let target = self.unpack_signal_assign_target(scope_id, target)?;
			let tyctx = match target {
				hir::SigAssignTarget::Name(id) => TypeCtx::TypeOf(id.into()),
				hir::SigAssignTarget::Aggregate => unimplemented!(),
			};
			let kind = self.unpack_signal_assign_mode(scope_id, mode, &tyctx)?;
			if guarded {
				self.emit(
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
				kind: kind.value,
				kind_span: kind.span,
			}))
		}
		_ => unreachable!()
	}
});

impl_make!(self, id: ArrayTypeIndexRef => &Spanned<hir::ArrayTypeIndex> {
	let (scope_id, ast) = self.ast(id);
	let ctx = TermContext::new(self, scope_id);
	let term = ctx.termify_expr(ast)?;
	if self.sb.trace_termification {
		self.emit(
			DiagBuilder2::note(format!("termified expr `{}`", ast.span.extract()))
			.span(ast.span)
			.add_note(format!("{:?}", term))
		);
	}
	let term = ctx.fold_term_as_type(term)?;
	let index = match term.value {
		Term::Range(dir, lb, rb) => {
			let lb = ctx.term_to_expr(*lb)?;
			let rb = ctx.term_to_expr(*rb)?;
			hir::ArrayTypeIndex::Range(dir, lb, rb)
		}
		Term::UnboundedRange(subterm) => {
			let tm = ctx.term_to_type_mark(*subterm)?;
			hir::ArrayTypeIndex::Unbounded(tm)
		}
		Term::TypeMark(..) | Term::SubtypeInd(..) => {
			let subty = ctx.term_to_subtype_ind(term)?.map(|i| self.intern_subtype_ind(i));
			hir::ArrayTypeIndex::Subtype(subty.value)
		}
		_ => {
			self.emit(
				DiagBuilder2::error(format!("`{}` is not a valid array index", term.span.extract()))
				.span(term.span)
			);
			debugln!("It is a {:#?}", term);
			return Err(());
		}
	};
	Ok(self.sb.arenas.hir.array_type_index.alloc(Spanned::new(index, ast.span)))
});

impl_make!(self, id: SubtypeIndRef => &hir::SubtypeInd {
	let (scope_id, ast) = self.ast(id);
	let ctx = TermContext::new(self, scope_id);
	let term = ctx.termify_subtype_ind(ast)?;
	Ok(self.sb.arenas.hir.subtype_ind.alloc(ctx.term_to_subtype_ind(term)?.value))
});

impl<'sb, 'ast, 'ctx> ScoreContext<'sb, 'ast, 'ctx> {
}

#[derive(Debug, PartialEq, Eq)]
pub enum Term {
	/// A term of the form `null`.
	Null,
	/// A term of the form `open`.
	Open,
	/// A term of the form `others`.
	Others,
	/// A term of the form `default`.
	Default,
	/// An integer literal.
	IntLit(BigInt),
	/// An unresolved name.
	Unresolved(ResolvableName),
	/// A term that refers to a definition.
	Ident(Spanned<Def>),
	/// A term that refers to a type or subtype definition.
	TypeMark(Spanned<TypeMarkRef>),
	/// A term that refers to an enum variant.
	Enum(Vec<Spanned<EnumRef>>),
	/// A term of the form `T.<name>`.
	Select(Subterm, Spanned<ResolvableName>),
	/// A term of the form `T.all`.
	SelectAll(Subterm),
	/// A term of the form `T (to|downto) T`.
	Range(Dir, Subterm, Subterm),
	/// A term of the form `T range T`.
	RangeSuffix(Subterm, Subterm),
	/// A term of the form `T range <>`.
	UnboundedRange(Subterm),
	/// A term of the form `[T] <type_mark> [T]`. The first optional subterm is
	/// the resolution indication, the second is the constraint.
	SubtypeInd(Spanned<TypeMarkRef>, Option<Subterm>, Option<Subterm>),
	/// A term of the form `(T) T`.
	PrefixParen(Subterm, Subterm),
	/// A term of the form `T (T)`.
	SuffixParen(Subterm, Subterm),
	/// A term of the form `(T,T,…)`.
	Paren(Vec<Spanned<Term>>),
	/// A term of the form `(T|T|… => T, T|T|… => T, …)`.
	Aggregate(Vec<(Vec<Spanned<Term>>, Spanned<Term>)>),
	/// A term of the form `op T`.
	Unary(Spanned<hir::UnaryOp>, Subterm),
	/// A term of the form `T op T`.
	Binary(Spanned<hir::BinaryOp>, Subterm, Subterm),
}

pub type Subterm = Box<Spanned<Term>>;

/// A context within which termification can occur.
pub struct TermContext<'sbc, 'sb: 'sbc, 'ast: 'sb, 'ctx: 'sb> {
	/// The underlying scoreboard context.
	pub ctx: &'sbc ScoreContext<'sb, 'ast, 'ctx>,
	/// The scope within which the terms will resolve their names.
	pub scope: ScopeRef,
}

impl<'sbc, 'sb, 'ast, 'ctx> DiagEmitter for TermContext<'sbc, 'sb, 'ast, 'ctx> {
	fn emit(&self, diag: DiagBuilder2) {
		self.ctx.emit(diag)
	}
}

impl<'sbc, 'sb, 'ast, 'ctx> TermContext<'sbc, 'sb, 'ast, 'ctx> {
	/// Create a new termification context.
	pub fn new(ctx: &'sbc ScoreContext<'sb, 'ast, 'ctx>, scope: ScopeRef) -> TermContext<'sbc, 'sb, 'ast, 'ctx> {
		TermContext {
			ctx: ctx,
			scope: scope,
		}
	}

	/// Perform term folding.
	///
	/// This is a post-processing step that should be applied to all terms once
	/// they are constructed. Folding applies transformations to the terms, e.g.
	/// changing `Ident(Type|Subtype)` to `TypeMark`, or gobbling up subtype
	/// constraints where appropriate.
	pub fn fold(&self, term: Spanned<Term>) -> Spanned<Term> {
		let new = match term.value {
			Term::Ident(Spanned{ value: Def::Type(id), span }) => {
				Term::TypeMark(Spanned::new(id.into(), span))
			}
			Term::Ident(Spanned{ value: Def::Subtype(id), span }) => {
				Term::TypeMark(Spanned::new(id.into(), span))
			}
			other => other
		};
		Spanned::new(new, term.span)
	}

	/// Map an AST subtype indication to a term.
	pub fn termify_subtype_ind(&self, subty: &'ast ast::SubtypeInd) -> Result<Spanned<Term>> {
		let name = self.termify_compound_name(&subty.name)?;
		let res = match subty.res {
			Some(ast::ResolInd::Exprs(ref paren_elems)) => Some(self.termify_paren_elems(paren_elems)?),
			Some(ast::ResolInd::Name(ref name)) => Some(self.termify_compound_name(name)?),
			None => None,
		};
		if let Some(res) = res {
			let sp = Span::union(name.span, res.span);
			Ok(Spanned::new(Term::PrefixParen(Box::new(res), Box::new(name)), sp))
		} else {
			Ok(name)
		}
	}

	/// Map an AST expression to a term.
	pub fn termify_expr(&self, ast: &'ast ast::Expr) -> Result<Spanned<Term>> {
		let term = match ast.data {
			// Literals with optional unit.
			ast::LitExpr(ref lit, ref unit) => {
				let lit = self.termify_literal(Spanned::new(lit, ast.span))?;
				let unit = match *unit {
					Some(ref unit_name) => Some(self.termify_compound_name(unit_name)?),
					None => None,
				};
				if let Some(unit) = unit {
					unimp_msg!(self, "termification of physical type", unit.span());
				} else {
					return Ok(lit);
				}
			}
			ast::NameExpr(ref name) => return self.termify_compound_name(name),
			// ast::ResolExpr(ref paren_elems, ref name) => {
			// 	let name = self.termify_compound_name(name)?;
			// }
			// Ranges of the form `T to T` and `T downto T`.
			ast::BinaryExpr(ast::BinaryOp::Dir(d), ref lb, ref rb) => {
				Term::Range(d, self.termify_expr(lb)?.into(), self.termify_expr(rb)?.into())
			}
			ast::UnaryExpr(op, ref arg) => Term::Unary(
				self.ctx.lower_unary_op(Spanned::new(op, ast.span))?,
				self.termify_expr(arg)?.into(),
			),
			ast::BinaryExpr(op, ref lhs, ref rhs) => Term::Binary(
				self.ctx.lower_binary_op(Spanned::new(op, ast.span))?,
				self.termify_expr(lhs)?.into(),
				self.termify_expr(rhs)?.into(),
			),
			ast::NullExpr => Term::Null,
			ast::OpenExpr => Term::Open,
			ast::OthersExpr => Term::Others,
			ast::DefaultExpr => Term::Default,
			ref wrong => {
				self.emit(
					DiagBuilder2::bug(format!("termification of expression `{}` not implemented", ast.span.extract()))
					.span(ast.span)
					.add_note(format!("{:?}", wrong))
				);
				return Err(());
			}
		};
		Ok(self.fold(Spanned::new(term, ast.span)))
	}

	/// Map an AST literal to a term.
	pub fn termify_literal(&self, ast: Spanned<&'ast Literal>) -> Result<Spanned<Term>> {
		Ok(Spanned::new(match *ast.value {
			Literal::Abstract(base, int, frac, exp) => {
				let base = match base {
					Some(base) => match base.as_str().parse() {
						Ok(base) => base,
						Err(_) => {
							self.emit(
								DiagBuilder2::error(format!("`{}` is not a valid base for a number literal", base))
								.span(ast.span)
							);
							return Err(());
						}
					},
					None => 10,
				};
				let int = match BigInt::parse_bytes(int.as_str().as_bytes(), base) {
					Some(v) => v,
					None => {
						self.emit(
							DiagBuilder2::error(format!("`{}` is not a valid base-{} integer", int, base))
							.span(ast.span)
						);
						return Err(());
					}
				};

				// Parse the rest of the number.
				if frac.is_none() && exp.is_none() {
					Term::IntLit(int)
				} else {
					self.emit(
						DiagBuilder2::bug("Float literals not yet supported")
						.span(ast.span)
					);
					return Err(());
				}
			}
			ref wrong => {
				self.emit(
					DiagBuilder2::bug(format!("termification of literal `{}` not implemented", ast.span.extract()))
					.span(ast.span)
					.add_note(format!("{:?}", wrong))
				);
				return Err(());
			}
		}, ast.span))
	}

	/// Map an AST compound name to a term.
	pub fn termify_compound_name(&self, ast: &'ast ast::CompoundName) -> Result<Spanned<Term>> {
		// Map the primary name.
		let mut term = self.fold(self.termify_name(
			self.ctx.resolvable_from_primary_name(&ast.primary)?
		)?);

		// For each name part, wrap the term in another layer. Like an onion.
		for part in &ast.parts {
			term = self.fold(match *part {
				ast::NamePart::Select(ref primary) => {
					let n = self.ctx.resolvable_from_primary_name(primary)?;
					let sp = Span::union(term.span, n.span);
					Spanned::new(Term::Select(Box::new(term), n), sp)
				}
				ast::NamePart::SelectAll(span) => {
					let sp = Span::union(term.span, span);
					Spanned::new(Term::SelectAll(Box::new(term)), sp)
				}
				ast::NamePart::Signature(ref sig) => {
					unimp_msg!(self, "termification of signature suffix", sig.span);
				}
				ast::NamePart::Attribute(ident) => {
					let attr = self.termify_name(Spanned::new(ident.name.into(), ident.span))?;
					match attr.value {
						// TODO: Enable this as soon as we handle attribute
						// declarations.
						// Term::Ident(Spanned { value: Def::Attr(id), span }) => {
						//	let sp = Span::union(term.span, attr.span);
						// 	Spanned::new(Term::Attribute(Box::new(term), Spanned::new(id, span)), sp)
						// }
						Term::Ident(other) => {
							self.emit(
								DiagBuilder2::error(format!("`{}` is not an attribute name", ident.name))
								.span(ident.span)
								.add_note("Declared here:")
								.span(other.span)
							);
							return Err(());
						}
						_ => unreachable!(),
					}
				}
				ast::NamePart::Call(ref paren_elems) => {
					let subterm = self.termify_paren_elems(paren_elems)?;
					let sp = Span::union(term.span, subterm.span);
					Spanned::new(Term::SuffixParen(Box::new(term), Box::new(subterm)), sp)
				}
				ast::NamePart::Range(ref expr) => {
					if expr.data == ast::BoxExpr {
						let sp = Span::union(term.span, expr.span);
						Spanned::new(Term::UnboundedRange(Box::new(term)), sp)
					} else {
						let expr = self.termify_expr(expr)?;
						let sp = Span::union(term.span, expr.span);
						Spanned::new(Term::RangeSuffix(Box::new(term), Box::new(expr)), sp)
					}
				}
			});
		}

		Ok(term)
	}

	/// Map a resolvable name to a term.
	///
	/// This function is the bottom of the pit. Names are resolved here and
	/// mapped to the corresponding term. Calling functions may then proceed to
	/// handle the term as they see fit, usually inspecting what exact kind the
	/// term is of.
	pub fn termify_name(&self, name: Spanned<ResolvableName>) -> Result<Spanned<Term>> {
		// First resolve the name to a list of definitions.
		let mut defs = self.ctx.resolve_name(name, self.scope, false, true)?;
		if defs.is_empty() {
			return Ok(name.map(Term::Unresolved));
		}

		fn is_enum(def: &Spanned<Def>) -> bool { match def.value { Def::Enum(..) => true, _ => false }}
		let all_enum = defs.iter().all(is_enum);

		// Handle overloading. Basically if the definitions are all enum fields
		// or functions, that's fine. For everything else the name must be
		// unique.
		let first_def = defs.pop().unwrap();
		let term = match first_def.value {
			Def::Enum(id) if all_enum => {
				let mut ids = vec![Spanned::new(id, first_def.span)];
				for def in defs {
					match def.value {
						Def::Enum(id) => ids.push(Spanned::new(id, def.span)),
						_ => unreachable!(),
					}
				}
				Term::Enum(ids)
			}
			// TODO: Handle the function case.
			_ if !defs.is_empty() => {
				let mut d = DiagBuilder2::error(format!("`{}` is ambiguous", name.value)).span(name.span);
				d = d.add_note("Found the following definitions:");
				d = d.span(first_def.span());
				for def in defs {
					d = d.span(def.span());
				}
				self.emit(d);
				return Err(());
			}
			_ => Term::Ident(first_def),
		};

		Ok(self.fold(Spanned::new(term, name.span)))
	}

	/// Map multiple parenthesis elements to a term.
	pub fn termify_paren_elems(&self, elems: &'ast ast::ParenElems) -> Result<Spanned<Term>> {
		let is_aggregate = elems.value.iter().any(|e| !e.choices.is_empty());
		let term = if is_aggregate {
			Term::Aggregate(elems.value.iter().map(|e| Ok((
				e.choices.iter().map(|c| self.termify_expr(c)).collect::<Result<Vec<_>>>()?,
				self.termify_expr(&e.expr)?
			))).collect::<Result<Vec<_>>>()?)
		} else {
			Term::Paren(elems.value
				.iter()
				.map(|e| self.termify_expr(&e.expr))
				.collect::<Result<Vec<_>>>()?
			)
		};
		Ok(self.fold(Spanned::new(term, elems.span)))
	}

	/// Map a latent name to a term.
	pub fn termify_latent_name(&self, name: LatentName<'ast>) -> Result<Spanned<Term>> {
		match name {
			LatentName::Simple(n) => self.termify_name(n.map_into()),
			LatentName::Primary(n) => self.termify_name(self.ctx.resolvable_from_primary_name(n)?),
			LatentName::Compound(n) => self.termify_compound_name(n),
		}
	}

	/// Map a term to an expression.
	pub fn term_to_expr(&self, term: Spanned<Term>) -> Result<ExprRef> {
		let data = match term.value {
			Term::IntLit(value) => {
				hir::ExprData::IntegerLiteral(ConstInt::new(None, value))
			}
			Term::Unary(op, arg) => {
				hir::ExprData::Unary(op, self.term_to_expr(*arg)?)
			}
			// TODO: Enable this as soon as the HIR accepts BinaryOp.
			// Term::Binary(op, lhs, rhs) => {
			// 	hir::ExprData::Binary(op, self.term_to_expr(*lhs)?, self.term_to_expr(*rhs)?)
			// }
			_ => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is not a valid expression", term.span.extract()))
					.span(term.span)
				);
				debugln!("It is a {:#?}", term);
				return Err(());
			}
		};
		let hir = hir::Expr {
			parent: self.scope,
			span: term.span,
			data: data
		};
		let id = ExprRef(NodeId::alloc());
		self.ctx.set_hir(id, self.ctx.sb.arenas.hir.expr.alloc(hir));
		Ok(id)
	}

	/// Map a term to a type mark.
	pub fn term_to_type_mark(&self, term: Spanned<Term>) -> Result<Spanned<TypeMarkRef>> {
		match term.value {
			Term::TypeMark(tm) => Ok(tm),
			_ => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is not a type or subtype", term.span.extract()))
					.span(term.span)
				);
				debugln!("It is a {:#?}", term);
				return Err(());
			}
		}
	}

	/// Perform term folding expecting to yield a type.
	///
	/// This is a pre-processing step on terms. It is applied as soon as it is
	/// clear that a certain term should yield a type, e.g. when mapping to a
	/// subtype indication. This function performs certain precedence swaps and
	/// combines terms into higher level ones, e.g. `Term::SubtypeInd`.
	fn fold_term_as_type(&self, term: Spanned<Term>) -> Result<Spanned<Term>> {
		let (new, new_term) = match term.value {
			Term::Unresolved(name) => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is unknown", name))
					.span(term.span)
				);
				return Err(());
			}
			Term::RangeSuffix(subterm, range) => {
				let subterm = self.fold_term_as_type(*subterm)?;
				let range = self.fold_term_as_type(*range)?;
				match subterm.value {
					// Fold `TypeMark range T` to `SubtypeInd`.
					Term::TypeMark(tm) => (true, Term::SubtypeInd(tm, None, Some(Box::new(range)))),
					// Fold `SubtypeInd range T` to `SubtypeInd`.
					Term::SubtypeInd(tm, resol, Some(con)) => {
						let sp = Span::union(con.span, range.span);
						let new_con = Spanned::new(Term::RangeSuffix(con, Box::new(range)), sp);
						(true, Term::SubtypeInd(tm, resol, Some(Box::new(new_con))))
					}
					_ => (false, Term::RangeSuffix(Box::new(subterm), Box::new(range))),
				}
			}
			Term::SuffixParen(subterm, suffix) => {
				let subterm = self.fold_term_as_type(*subterm)?;
				let suffix = self.fold_term_as_type(*suffix)?;
				match subterm.value {
					// Fold `TypeMark (T)` to `SubtypeInd`.
					Term::TypeMark(tm) => (true, Term::SubtypeInd(tm, None, Some(Box::new(suffix)))),
					// Fold `SubtypeInd (T)` to `SubtypeInd`.
					Term::SubtypeInd(tm, resol, Some(con)) => {
						let sp = Span::union(con.span, suffix.span);
						let new_con = Spanned::new(Term::SuffixParen(con, Box::new(suffix)), sp);
						(true, Term::SubtypeInd(tm, resol, Some(Box::new(new_con))))
					}
					// Fold `SubtypeInd (T)` to `SubtypeInd`.
					Term::SubtypeInd(tm, resol, None) => {
						(true, Term::SubtypeInd(tm, resol, Some(Box::new(suffix))))
					}
					_ => (false, Term::SuffixParen(Box::new(subterm), Box::new(suffix))),
				}
			}
			others => (false, others)
		};
		let new_term = Spanned::new(new_term, term.span);
		if new {
			self.fold_term_as_type(new_term)
		} else {
			Ok(new_term)
		}
	}

	/// Map a term to a subtype indication.
	pub fn term_to_subtype_ind(&self, term: Spanned<Term>) -> Result<Spanned<hir::SubtypeInd>> {
		let term = self.fold_term_as_type(term)?;
		let (tm, resol, con) = match term.value {
			Term::SubtypeInd(tm, resol, con) => (tm, resol, con),
			Term::TypeMark(tm) => (tm, None, None),
			_ => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is not a subtype indication", term.span.extract()))
					.span(term.span)
				);
				debugln!("It is a {:#?}", term);
				return Err(());
			}
		};
		let _resol = match resol {
			Some(x) => Some(self.term_to_resolution_indication(*x)?),
			None => None,
		};
		let con = match con {
			Some(x) => Some(self.term_to_constraint(*x)?),
			None => None,
		};
		Ok(Spanned::new(hir::SubtypeInd {
			span: term.span,
			type_mark: tm,
			// TODO: Track resolution indication.
			constraint: con,
		}, term.span))
		// let id = SubtypeIndRef::new(NodeId::alloc());
		// self.ctx.set_hir(id, self.ctx.sb.arenas.hir.subtype_ind.alloc(hir));
		// Ok(Spanned::new(id, term.span))
	}

	/// Map a term to a resolution indication.
	pub fn term_to_resolution_indication(&self, term: Spanned<Term>) -> Result<Spanned<()>> {
		self.emit(
			DiagBuilder2::bug(format!("interpretation of `{}` as a resolution indication not implemented", term.span.extract()))
			.span(term.span)
		);
		Err(())
	}

	/// Map a term to a constraint.
	pub fn term_to_constraint(&self, term: Spanned<Term>) -> Result<Spanned<hir::Constraint>> {
		// Handle range constraints.
		match term.value {
			Term::Range(..) => return Ok(self.term_to_range(term)?.map(|r| hir::Constraint::Range(r))),
			_ => ()
		};

		// Unpack the optional element constraint on array constraints.
		let (term, elem) = match term.value {
			Term::RangeSuffix(subterm, con) | Term::SuffixParen(subterm, con) => (*subterm, Some(*con)),
			_ => (term, None),
		};

		// Otherwise handle the array and record constraint cases.
		match term.value {
			Term::Paren(terms) => {
				let any_records = terms.iter().any(|t| match t.value {
					Term::SuffixParen(..) => true,
					_ => false,
				});
				if any_records && elem.is_none() {
					self.term_to_record_constraint(term.span, terms).map(|t| t.map_into())
				} else {
					self.term_to_array_constraint(term.span, terms, elem).map(|t| t.map_into())
				}
			}
			_ => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is not a valid constraint", term.span.extract()))
					.span(term.span)
					.add_note("Did you mean a range constraint (`range ...`) or an array or record constraint (`(...)`)? See IEEE 1076-2008 section 6.3.")
				);
				debugln!("It is a {:#?}", term);
				return Err(());
			}
		}
	}

	/// Map a term to an array constraint.
	pub fn term_to_array_constraint(
		&self,
		span: Span,
		terms: Vec<Spanned<Term>>,
		elem: Option<Spanned<Term>>
	) -> Result<Spanned<hir::ArrayConstraint>> {
		if terms.is_empty() {
			self.emit(
				DiagBuilder2::error(format!("array constraint cannot be empty"))
				.span(span)
			);
			return Err(());
		}
		let indices = if terms.len() == 1 && terms[0].value == Term::Open {
			vec![]
		} else {
			terms.into_iter().map(|e| self.term_to_discrete_range(e)).collect::<Result<Vec<_>>>()?
		};
		let elem = match elem {
			Some(e) => Some(self.term_to_element_constraint(e)?),
			None => None,
		};
		Ok(Spanned::new(hir::ArrayConstraint {
			span: span,
			index: indices,
			elem: elem.map(|e| Box::new(e)),
		}, span))
	}

	/// Map a term to a record constraint.
	pub fn term_to_record_constraint(
		&self,
		span: Span,
		terms: Vec<Spanned<Term>>
	) -> Result<Spanned<hir::RecordConstraint>> {
		if terms.is_empty() {
			self.emit(
				DiagBuilder2::error(format!("record constraint cannot be empty"))
				.span(span)
			);
			return Err(());
		}
		let mut fields = Vec::new();
		let mut has_fails = false;
		let mut used_names = HashMap::new();
		for term in terms {
			// Make sure that the term is of the form `field (constraint)`.
			let (name, con) = match term.value {
				Term::SuffixParen(name, con) => (name, *con),
				_ => {
					self.emit(
						DiagBuilder2::error(format!("`{}` is not a valid constraint for a record element", term.span.extract()))
						.span(term.span)
						.add_note("Element constraints must be of the form `name (constraint)`. See IEEE 1076-2008 section 5.3.3.")
					);
					debugln!("It is a {:#?}", term.value);
					has_fails = true;
					continue;
				}
			};
			let name = match name.value {
				Term::Unresolved(ResolvableName::Ident(i)) => Spanned::new(i, name.span),
				_ => {
					self.emit(
						DiagBuilder2::error(format!("`{}` is not a valid record element name", name.span.extract()))
						.span(name.span)
					);
					debugln!("It is a {:#?}", name.value);
					has_fails = true;
					continue;
				}
			};

			// Make sure a field is not constrained twice.
			if let Some(&span) = used_names.get(&name.value) {
				self.emit(
					DiagBuilder2::error(format!("element `{}` has already been constrained", name.value))
					.span(name.span)
					.add_note("Previous constraint was here:")
					.span(span)
				);
				has_fails = true;
				continue;
			} else {
				used_names.insert(name.value, name.span);
			}

			// Parse the constraint.
			fields.push((name, Box::new(self.term_to_element_constraint(con)?)));
		}
		if has_fails {
			return Err(());
		}
		Ok(Spanned::new(hir::RecordConstraint {
			span: span,
			elems: fields,
		}, span))
	}

	/// Map a term to an element constraint.
	pub fn term_to_element_constraint(&self, term: Spanned<Term>) -> Result<Spanned<hir::ElementConstraint>> {
		let con = self.term_to_constraint(term)?;
		Ok(Spanned::new(match con.value {
			hir::Constraint::Array(c) => c.into(),
			hir::Constraint::Record(c) => c.into(),
			_ => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is not a valid element constraint", con.span.extract()))
					.span(con.span)
					.add_note("Did you mean an array or record constraint (`(...)`)? See IEEE 1076-2008 section 6.3.")
				);
				debugln!("It is a {:#?}", con);
				return Err(());
			}
		}, con.span))
	}

	/// Map a term to a discrete range.
	pub fn term_to_discrete_range(&self, term: Spanned<Term>) -> Result<Spanned<hir::DiscreteRange>> {
		let term = self.fold_term_as_type(term)?;
		Ok(match term.value {
			Term::SubtypeInd(..) | Term::TypeMark(..) => self.term_to_subtype_ind(term)?.map(|i| self.ctx.intern_subtype_ind(i)).map_into(),
			Term::Range(..) => self.term_to_range(term)?.map_into(),
			_ => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is not a valid discrete range", term.span.extract()))
					.span(term.span)
					.add_note("A discrete range can be one of the following:")
					.add_note("- a subtype indication of the form `[resolution] type_mark [constraint]`")
					.add_note("- a range of the form `a to b` or `a downto b`")
					.add_note("- a range attribute of the form `T'range`")
					.add_note("See IEEE 1076-2008 section 5.3.2.1.")
				);
				debugln!("It is a {:#?}", term);
				return Err(());
			}
		})
	}

	/// Map a term to a range.
	pub fn term_to_range(&self, term: Spanned<Term>) -> Result<Spanned<hir::Range>> {
		Ok(Spanned::new(match term.value {
			// Term::Attr(..) => ...
			Term::Range(dir, lb, rb) => hir::Range::Immediate(
				dir,
				self.term_to_expr(*lb)?,
				self.term_to_expr(*rb)?
			),
			_ => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is not a valid range", term.span.extract()))
					.span(term.span)
					.add_note("A range can be one of the following:")
					.add_note("- an ascending range of the form `a to b`")
					.add_note("- a descending range of the form `a downto b`")
					.add_note("- a range attribute of the form `T'range`")
					.add_note("See IEEE 1076-2008 section 5.2.1.")
				);
				debugln!("It is a {:#?}", term);
				return Err(());
			}
		}, term.span))
	}
}

// Lower a subprogram declaration to HIR.
impl_make!(self, id: SubprogDeclRef => &hir::Subprog {
	let (scope_id, ast) = self.ast(id);
	let spec = self.lower_subprog_spec(id.into(), &ast.spec)?;
	Ok(self.sb.arenas.hir.subprog.alloc(hir::Subprog {
		parent: scope_id,
		spec: spec,
	}))
});

// Lower a subprogram body to HIR.
impl_make!(self, id: SubprogBodyRef => &hir::SubprogBody {
	let (scope_id, ast) = self.ast(id);
	let spec = self.lower_subprog_spec(id.into(), &ast.spec)?;
	let subprog = self.unpack_subprog_name((&ast.spec.name).into(), scope_id)?;
	let (decls, stmts) = match ast.data {
		ast::SubprogData::Body { ref decls, ref stmts } => (decls, stmts),
		_ => unreachable!(),
	};
	let decls = self.unpack_subprog_decls(scope_id, decls)?;
	let stmts = self.unpack_sequential_stmts(scope_id, stmts, "a subprogram")?;
	Ok(self.sb.arenas.hir.subprog_body.alloc(hir::SubprogBody {
		parent: scope_id,
		spec: spec,
		subprog: subprog,
		decls: decls,
		stmts: stmts,
	}))
});

// Lower a subprogram instantiation to HIR.
impl_make!(self, id: SubprogInstRef => &hir::SubprogInst {
	let (_scope_id, ast) = self.ast(id);
	unimp_msg!(self, "subprogram instantiations", ast.span);
	// let spec = self.lower_subprog_spec(id.into(), &ast.spec)?;
	// Ok(self.sb.arenas.hir.subprog_inst.alloc(hir::SubprogInst {
	// 	parent: scope_id,
	// 	kind: ,
	// 	name: ,
	// 	subprog: ,
	// 	generic_map: ,
	// }))
});

impl_make!(self, id: LatentTypeMarkRef => Spanned<TypeMarkRef> {
	let (scope_id, ast) = self.ast(id);
	let ctx = TermContext::new(self, scope_id);
	let term = ctx.termify_latent_name(ast)?;
	ctx.term_to_type_mark(term)
});
