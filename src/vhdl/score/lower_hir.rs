// Copyright (c) 2017 Fabian Schuiki

//! This module implements lowering of the AST to the HIR.
//!
//! Note that unpacking here refers to the process of taking a reference to an
//! AST node, creating an ID for it, and adding it to the AST table for later
//! lowering to HIR.

use common::score::NodeRef;
use score::*;
use syntax::lexer::token::Literal;
use make_ctx::MakeContext;
use add_ctx::AddContext;
use term::*;
use op::*;

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

impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
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
		// let id = SubtypeIndRef::new(NodeId::alloc());
		// self.set_ast(id, (scope_id, ast));
		// Ok(id)
		let ctx = AddContext::new(self, scope_id);
		ctx.add_subtype_ind(ast)
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

	/// Unpack a slice of AST declarative items into a list of items admissible
	/// in the declarative part of a block.
	///
	/// See IEEE 1076-2008 section 3.3.2.
	pub fn unpack_block_decls(&self, scope_id: ScopeRef, decls: &'ast [ast::DeclItem], container_name: &str) -> Result<Vec<DeclInBlockRef>> {
		let mut refs = Vec::new();
		let mut had_fails = false;

		let ctx = AddContext::new(self, scope_id);
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
							refs.extend(ctx.add_const_decl::<DeclInBlockRef>(decl)?);
						}
						ast::ObjKind::Signal => {
							refs.extend(ctx.add_signal_decl::<DeclInBlockRef>(decl)?);
						}
						ast::ObjKind::Var => {
							self.emit(
								DiagBuilder2::error(format!("not a shared variable; only shared variables may appear in {}", container_name))
								.span(decl.human_span())
							);
							had_fails = true;
						}
						ast::ObjKind::SharedVar => {
							refs.extend(ctx.add_var_decl::<DeclInBlockRef>(decl)?);
						}
						ast::ObjKind::File => {
							refs.extend(ctx.add_file_decl::<DeclInBlockRef>(decl)?);
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
				ast::DeclItem::CfgSpec(ref decl) => {
					let subid = CfgSpecRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::DisconDecl(ref decl) => {
					let subid = DisconSpecRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::GroupDecl(ref decl) => {
					match decl.data {
						ast::GroupData::Decl(..) => {
							let subid = GroupDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::GroupData::Temp{..} => {
							let subid = GroupTempRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
					}
				}
				ast::DeclItem::UseClause(..) => (),
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
	/// in the declarative part of a process.
	///
	/// See IEEE 1076-2008 section 11.3.
	pub fn unpack_process_decls(
		&self,
		scope_id: ScopeRef,
		decls: &'ast [ast::DeclItem],
		container_name: &str
	) -> Result<Vec<DeclInProcRef>> {
		let mut refs = Vec::new();
		let mut had_fails = false;

		let ctx = AddContext::new(self, scope_id);
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
							refs.extend(ctx.add_const_decl::<DeclInProcRef>(decl)?);
						}
						ast::ObjKind::Signal => {
							self.emit(
								DiagBuilder2::error(format!("a signal declaration cannot appear in {}", container_name))
								.span(decl.human_span())
							);
							had_fails = true;
						}
						ast::ObjKind::SharedVar => {
							self.emit(
								DiagBuilder2::error(format!("not a variable; shared variables may not appear in {}", container_name))
								.span(decl.human_span())
							);
							had_fails = true;
						}
						ast::ObjKind::Var => {
							refs.extend(ctx.add_var_decl::<DeclInProcRef>(decl)?);
						}
						ast::ObjKind::File => {
							refs.extend(ctx.add_file_decl::<DeclInProcRef>(decl)?);
						}
					}
				}
				ast::DeclItem::AliasDecl(ref decl) => {
					let subid = AliasDeclRef(NodeId::alloc());
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
				ast::DeclItem::GroupDecl(ref decl) => {
					match decl.data {
						ast::GroupData::Decl(..) => {
							let subid = GroupDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::GroupData::Temp{..} => {
							let subid = GroupTempRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
					}
				}
				ast::DeclItem::UseClause(..) => (),
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

		let ctx = AddContext::new(self, scope_id);
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
							refs.extend(ctx.add_const_decl::<DeclInSubprogRef>(decl)?);
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
							refs.extend(ctx.add_var_decl::<DeclInSubprogRef>(decl)?);
						}
						ast::ObjKind::File => {
							refs.extend(ctx.add_file_decl::<DeclInSubprogRef>(decl)?);
						}
					}
				}
				ast::DeclItem::AliasDecl(ref decl) => {
					let subid = AliasDeclRef(NodeId::alloc());
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
				ast::DeclItem::GroupDecl(ref decl) => {
					match decl.data {
						ast::GroupData::Decl(..) => {
							let subid = GroupDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::GroupData::Temp{..} => {
							let subid = GroupTempRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
					}
				}
				ast::DeclItem::UseClause(..) => (),
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

		let ctx = AddContext::new(self, scope_id);
		ctx.add_seq_stmts(stmts, container_name)
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
			if !elem.choices.value.is_empty() {
				let span = Span::union(elem.choices.value[0].span, elem.choices.value.last().unwrap().span);
				self.emit(
					DiagBuilder2::error(format!("`=>` not applicable in {}", context))
					.span(span)
				);
			}
			&elem.expr
		}).collect()
	}

	/// Lower an AST unary operator to a HIR unary operator.
	///
	/// Emits an error if the operator is not a valid unary operator.
	pub fn lower_unary_op(&self, ast: Spanned<ast::UnaryOp>) -> Result<Spanned<UnaryOp>> {
		let op = match ast.value {
			ast::UnaryOp::Not => UnaryOp::Not,
			ast::UnaryOp::Abs => UnaryOp::Abs,
			ast::UnaryOp::Sign(ast::Sign::Pos) => UnaryOp::Pos,
			ast::UnaryOp::Sign(ast::Sign::Neg) => UnaryOp::Neg,
			ast::UnaryOp::Logical(op) => UnaryOp::Logical(op),
			ast::UnaryOp::Condition => UnaryOp::Cond,
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
	pub fn lower_binary_op(&self, ast: Spanned<ast::BinaryOp>) -> Result<Spanned<BinaryOp>> {
		let op = match ast.value {
			ast::BinaryOp::Logical(op) => BinaryOp::Logical(op),
			ast::BinaryOp::Rel(op) => BinaryOp::Rel(op),
			ast::BinaryOp::Match(op) => BinaryOp::Match(op),
			ast::BinaryOp::Shift(op) => BinaryOp::Shift(op),
			ast::BinaryOp::Add => BinaryOp::Add,
			ast::BinaryOp::Sub => BinaryOp::Sub,
			ast::BinaryOp::Concat => BinaryOp::Concat,
			ast::BinaryOp::Mul => BinaryOp::Mul,
			ast::BinaryOp::Div => BinaryOp::Div,
			ast::BinaryOp::Mod => BinaryOp::Mod,
			ast::BinaryOp::Rem => BinaryOp::Rem,
			ast::BinaryOp::Pow => BinaryOp::Pow,
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
		let kind = match (ast.kind, ast.purity) {
			(ast::SubprogKind::Proc, None) => hir::SubprogKind::Proc,
			(ast::SubprogKind::Func, None) |
			(ast::SubprogKind::Func, Some(ast::SubprogPurity::Pure)) => hir::SubprogKind::PureFunc,
			(ast::SubprogKind::Func, Some(ast::SubprogPurity::Impure)) => hir::SubprogKind::ImpureFunc,
			(ast::SubprogKind::Proc, Some(_)) => {
				self.emit(
					DiagBuilder2::error(format!("Procedure `{}` cannot be pure/impure", ast.name.span.extract()))
					.span(ast.name.span)
				);
				hir::SubprogKind::Proc
			}
		};
		let name = self.lower_subprog_name(kind, &ast.name)?;
		let mut generics = Vec::new();
		if let Some(ref gc) = ast.generic_clause {
			self.unpack_generics(scope_id, gc, &mut generics)?;
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
		Ok(hir::SubprogSpec {
			name: name,
			kind: kind,
			generics: generics,
			generic_map: generic_map,
			params: vec![],
			return_type: return_type,
		})
	}

	/// Lower the name of an AST subprogram to HIR and perform checks.
	pub fn lower_subprog_name(
		&self,
		kind: hir::SubprogKind,
		name: &'ast ast::PrimaryName,
	) -> Result<(Spanned<ResolvableName>)> {
		let name = self.resolvable_from_primary_name(&name)?;
		if name.value.is_bit() {
			self.emit(
				DiagBuilder2::error(format!("`{}` is not a valid subprogram name", name.value))
				.span(name.span)
				.add_note("Bit literals cannot be used as subprogram names. See IEEE 1076-2008 section 4.2.1.")
			);
			return Err(());
		}
		if kind == hir::SubprogKind::Proc && !name.value.is_ident() {
			self.emit(
				DiagBuilder2::error(format!("`{}` overload must be a function", name.value))
				.span(name.span)
				.add_note("Procedures cannot overload operators. Use a function. See IEEE 1076-2008 section 4.2.1.")
			);
			return Err(());
		}
		Ok(name)
	}

	/// Unpack generics from a list of interface declarations.
	///
	/// See IEEE 1076-2008 section 6.5.6.1.
	pub fn unpack_generics(&self, scope_id: ScopeRef, decls: &'ast [ast::IntfDecl], into: &mut Vec<GenericRef>) -> Result<()> {
		let ctx = AddContext::new(self, scope_id);
		let mut had_fails = false;
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
					let ty = ctx.add_subtype_ind(&decl.ty)?;
					// let ty = SubtypeIndRef(NodeId::alloc());
					// self.set_ast(ty, (scope_id, &decl.ty));
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
					had_fails = true;
				}
			}
		}
		if had_fails {
			Err(())
		} else {
			Ok(())
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
	let ctx = AddContext::new(self, id.into());
	for decl in &ast.decls {
		match *decl {
			// Port clauses
			ast::DeclItem::PortgenClause(_, Spanned{ value: ast::PortgenKind::Port, span }, ref decls) => {
				// For ports only signal interface declarations are allowed.
				port_spans.push(span);
				for decl in &decls.value {
					match *decl {
						ast::IntfDecl::ObjDecl(ref decl @ ast::IntfObjDecl{ kind: ast::IntfObjKind::Signal, .. }) => {
							let ty = ctx.add_subtype_ind(&decl.ty)?;
							// let ty = SubtypeIndRef(NodeId::alloc());
							// self.set_ast(ty, (id.into(), &decl.ty));
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
				self.unpack_generics(id.into(), &decls.value, &mut entity.generics)?;
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
	let ctx = AddContext::new(self, scope_id);
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
						self.emit(
							DiagBuilder2::error(format!("a {} cannot appear in a package declaration", decl.desc()))
							.span(decl.human_span())
							.add_note("Only subprogram declarations or instantiations can appear in a package declaration. See IEEE 1076-2008 section 4.7.")
						);
						had_fails = true;
						continue;
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
						decls.extend(ctx.add_const_decl::<DeclInPkgRef>(decl)?);
					}
					ast::ObjKind::Signal => {
						decls.extend(ctx.add_signal_decl::<DeclInPkgRef>(decl)?);
					}
					ast::ObjKind::SharedVar => {
						self.emit(
							DiagBuilder2::error("not a variable; shared variables may not appear in a package declaration")
							.span(decl.human_span())
						);
						had_fails = true;
					}
					ast::ObjKind::Var => {
						decls.extend(ctx.add_var_decl::<DeclInPkgRef>(decl)?);
					}
					ast::ObjKind::File => {
						decls.extend(ctx.add_file_decl::<DeclInPkgRef>(decl)?);
					}
				}
			}
			ast::DeclItem::AliasDecl(ref decl) => {
				let subid = AliasDeclRef(NodeId::alloc());
				self.set_ast(subid, (scope_id, decl));
				decls.push(subid.into());
			}
			ast::DeclItem::CompDecl(ref decl) => {
				let subid = CompDeclRef(NodeId::alloc());
				self.set_ast(subid, (scope_id, decl));
				decls.push(subid.into());
			}
			ast::DeclItem::AttrDecl(ref decl) => {
				match decl.data {
					ast::AttrData::Decl(..) => {
						let subid = AttrDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
					ast::AttrData::Spec{..} => {
						let subid = AttrSpecRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
				}
			}
			ast::DeclItem::DisconDecl(ref decl) => {
				let subid = DisconSpecRef(NodeId::alloc());
				self.set_ast(subid, (scope_id, decl));
				decls.push(subid.into());
			}
			ast::DeclItem::GroupDecl(ref decl) => {
				match decl.data {
					ast::GroupData::Decl(..) => {
						let subid = GroupDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
					ast::GroupData::Temp{..} => {
						let subid = GroupTempRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
				}
			}
			ast::DeclItem::UseClause(..) => (),
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
	let ctx = AddContext::new(self, scope_id);
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
						decls.extend(ctx.add_const_decl::<DeclInPkgBodyRef>(decl)?);
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
						decls.extend(ctx.add_var_decl::<DeclInPkgBodyRef>(decl)?);
					}
					ast::ObjKind::File => {
						decls.extend(ctx.add_file_decl::<DeclInPkgBodyRef>(decl)?);
					}
				}
			}
			ast::DeclItem::AliasDecl(ref decl) => {
				let subid = AliasDeclRef(NodeId::alloc());
				self.set_ast(subid, (scope_id, decl));
				decls.push(subid.into());
			}
			ast::DeclItem::AttrDecl(ref decl) => {
				match decl.data {
					ast::AttrData::Decl(..) => {
						let subid = AttrDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
					ast::AttrData::Spec{..} => {
						let subid = AttrSpecRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
				}
			}
			ast::DeclItem::GroupDecl(ref decl) => {
				match decl.data {
					ast::GroupData::Decl(..) => {
						let subid = GroupDeclRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
					ast::GroupData::Temp{..} => {
						let subid = GroupTempRef(NodeId::alloc());
						self.set_ast(subid, (scope_id, decl));
						decls.push(subid.into());
					}
				}
			}
			ast::DeclItem::UseClause(..) => (),
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
		ast::LitExpr(..) => {
			let term_ctx = TermContext::new(self, scope_id);
			let term = term_ctx.termify_expr(ast)?;
			term_ctx.term_to_expr_raw(term)?.data
		}

		// Unary operators.
		ast::UnaryExpr(op, ref arg) => {
			let op = self.lower_unary_op(Spanned::new(op, ast.span))?;
			let subid = ExprRef(NodeId::alloc());
			self.set_ast(subid, (scope_id, arg.as_ref()));
			hir::ExprData::Unary(op, vec![], subid)
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
				if let Some(tyctx) = self.type_context_resolved(id)? {
					let ty = self.deref_named_type(tyctx)?;
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
						// let ctx = AddContext::new(self, scope_id);
						// let lb = ctx.add_expr(lb_expr)?;
						// let rb = ctx.add_expr(rb_expr)?;
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
				if let Some(ref units) = *units {
					// Determine the primary unit.
					let mut prim_iter = units
						.iter()
						.enumerate()
						.filter(|&(_, &(_, ref expr))| expr.is_none())
						.map(|(index, &(name, _))| (index, name));
					let primary = match prim_iter.next() {
						Some(u) => u,
						None => {
							self.emit(
								DiagBuilder2::error(format!("physical type `{}` has no primary unit", ast.name.value))
								.span(ast.span)
								.add_note("A physical type must have a primary unit of the form `<name>;`. See IEEE 1076-2008 section 5.2.4.")
							);
							return Err(());
						}
					};
					let mut had_fails = false;
					for (_, name) in prim_iter {
						self.emit(
							DiagBuilder2::error(format!("physical type `{}` has multiple primary units", ast.name.value))
							.span(name.span)
							.add_note("A physical type cannot have multiple primary units. See IEEE 1076-2008 section 5.2.4.")
						);
						had_fails = true;
					}
					if had_fails {
						return Err(());
					}
					debugln!("primary unit {:#?}", primary);

					// Determine the units and how they are defined with respect
					// to each other.
					let term_ctx = TermContext::new(self, scope_id);
					let table = units
						.iter()
						.map(|&(name, ref expr)|{
							let rel = if let Some(ref expr) = *expr {
								let term = term_ctx.termify_expr(expr)?;
								let (value, unit) = match term.value {
									Term::PhysLit(value, unit) => (value, unit),
									_ => {
										self.emit(
											DiagBuilder2::error(format!("`{}` is not a valid secondary unit", term.span.extract()))
											.span(term.span)
										);
										debugln!("It is a {:#?}", term.value);
										return Err(());
									}
								};
								if unit.value.0 != id {
									self.emit(
										DiagBuilder2::error(format!("`{}` is not a unit in the physical type `{}`", term.span.extract(), ast.name.value))
										.span(term.span)
										.add_note(format!("`{}` has been declared here:", term.span.extract()))
										.span(unit.span)
									);
								}
								Some((value, unit.value.1))
							} else {
								None
							};
							Ok((Spanned::new(name.name, name.span), rel))
						})
						.collect::<Vec<Result<_>>>()
						.into_iter()
						.collect::<Result<Vec<_>>>()?;

					// Determine the scale of each unit with respect to the
					// primary unit.
					let scale_table = table
						.iter()
						.map(|&(name, ref rel)|{
							let mut abs = BigInt::from(1);
							let mut rel_to = rel.as_ref();
							while let Some(&(ref scale, index)) = rel_to {
								abs = abs * scale;
								rel_to = table[index].1.as_ref();
							}
							(name, abs, rel.clone())
						})
						.collect::<Vec<_>>();

					hir::TypeData::Physical(dir, lb, rb, scale_table, primary.0)
				} else {
					hir::TypeData::Range(dir, lb, rb)
				}
			}

			// Enumeration types.
			ast::EnumType(ref elems) => {
				let mut lits = Vec::new();
				for elem in &elems.value {
					// Unpack the element. Make sure it only consists of an
					// expression that is either an identifier or a character
					// literal.
					let lit = if !elem.choices.value.is_empty() {
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
				let elem_subty = ctx.term_to_subtype_ind(subty)?.value;
				let add_ctx = AddContext::new(self, scope_id);
				let elem_subty = add_ctx.add_subtype_ind_hir(elem_subty)?;
				hir::TypeData::Array(indices, elem_subty)
			}

			ast::FileType(ref name) => {
				let ctx = TermContext::new(self, scope_id);
				let term = ctx.termify_compound_name(name)?;
				let tm = ctx.term_to_type_mark(term)?;
				hir::TypeData::File(tm)
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
			ref decls,
			ref stmts,
			postponed,
			..
		} => {
			// TODO: map sensititivty
			let decls = self.unpack_process_decls(id.into(), decls, "a process")?;
			let stmts = self.unpack_sequential_stmts(id.into(), stmts, "a process")?;
			Ok(self.sb.arenas.hir.process_stmt.alloc(hir::ProcessStmt {
				parent: scope_id,
				label: ast.label,
				postponed: postponed,
				sensitivity: hir::ProcessSensitivity::None,
				decls: decls,
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
			let subty = ctx.term_to_subtype_ind(term)?.value;
			let add_ctx = AddContext::new(self, scope_id);
			let subty = add_ctx.add_subtype_ind_hir(subty)?;
			hir::ArrayTypeIndex::Subtype(subty)
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

// impl_make!(self, id: SubtypeIndRef => &hir::SubtypeInd {
// 	let (scope_id, ast) = self.ast(id);
// 	let ctx = TermContext::new(self, scope_id);
// 	let term = ctx.termify_subtype_ind(ast)?;
// 	Ok(self.sb.arenas.hir.subtype_ind.alloc(ctx.term_to_subtype_ind(term)?.value))
// });

impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
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
	let decls = self.unpack_subprog_decls(id.into(), decls)?;
	let stmts = self.unpack_sequential_stmts(id.into(), stmts, "a subprogram")?;
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
	let (scope_id, ast) = self.ast(id);
	let kind = match ast.spec.kind {
		ast::SubprogKind::Proc => hir::SubprogKind::Proc,
		ast::SubprogKind::Func => hir::SubprogKind::PureFunc,
	};
	let name = self.lower_subprog_name(kind, &ast.spec.name)?;
	assert!(ast.spec.purity.is_none());
	assert!(ast.spec.generic_clause.is_none());
	assert!(ast.spec.generic_map.is_none());
	assert!(ast.spec.params.is_none());
	assert!(ast.spec.retty.is_none());
	let (target_name, generics) = match ast.data {
		ast::SubprogData::Inst { ref name, ref generics } => (name, generics),
		_ => unreachable!(),
	};
	let subprog = self.unpack_subprog_name(target_name.into(), scope_id)?;
	let generics = match *generics {
		Some(ref g) => self.unpack_generic_map(scope_id, g)?,
		None => vec![],
	};
	Ok(self.sb.arenas.hir.subprog_inst.alloc(hir::SubprogInst {
		parent: scope_id,
		kind: kind,
		name: name,
		subprog: subprog,
		generic_map: generics,
	}))
});

impl_make!(self, id: LatentTypeMarkRef => Spanned<TypeMarkRef> {
	let (scope_id, ast) = self.ast(id);
	let ctx = TermContext::new(self, scope_id);
	let term = ctx.termify_latent_name(ast)?;
	ctx.term_to_type_mark(term)
});
