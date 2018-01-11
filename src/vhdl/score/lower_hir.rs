// Copyright (c) 2017 Fabian Schuiki

//! This module implements lowering of the AST to the HIR.
//!
//! Note that unpacking here refers to the process of taking a reference to an
//! AST node, creating an ID for it, and adding it to the AST table for later
//! lowering to HIR.

use score::*;


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
			self.sb.hir_table.borrow_mut().set(id, hir);
			refs.push(id.into());
		}

		Ok(())
	}


	// /// Convert a compound name into an HIR expression.
	// pub fn compound_name_to_expr(&self, ast: &'ast ast::CompoundName, scope_id: ScopeRef) -> Result<&'ctx hir::Expr> {
	// 	// Map the primary name to a resolvable name, and wrap it in a name
	// 	// expression.
	// 	let primary = self.resolvable_from_primary_name(&ast.primary)?;
	// 	let mut expr: &'ctx hir::Expr = self.sb.arenas.hir.expr.alloc(hir::Expr{
	// 		parent: scope_id,
	// 		span: primary.span,
	// 		data: hir::ExprData::Name(primary.value),
	// 	});

	// 	// Map each name part recursively.
	// 	for part in &ast.parts {
	// 		// Allocate a node ID for the inner expression and store it away in
	// 		// the HIR table.
	// 		let inner = ExprRef::new(NodeId::alloc());
	// 		let inner_span = expr.span;
	// 		self.sb.hir_table.borrow_mut().set(inner, expr);

	// 		match *part {
	// 			ast::NamePart::Select(name) => {
	// 				let rn = self.resolvable_from_primary_name(&name)?;
	// 				expr = self.sb.arenas.hir.expr.alloc(hir::Expr{
	// 					parent: scope_id,
	// 					span: Span::union(inner_span, rn.span),
	// 					data: hir::ExprData::Select(inner, rn),
	// 				});
	// 			}

	// 			ast::NamePart::Signature(ref _sig) => unimplemented!(),

	// 			ast::NamePart::Attribute(ident) => {
	// 				expr = self.sb.arenas.hir.expr.alloc(hir::Expr{
	// 					parent: scope_id,
	// 					span: Span::union(inner_span, ident.span),
	// 					data: hir::ExprData::Attr(inner, Spanned::new(ident.name.into(), ident.span)),
	// 				});
	// 			}

	// 			// Call expressions can map to different things. First we need
	// 			// to know what type the callee has. Based on this, the list of
	// 			// arguments can be associated with the correct ports. Or in
	// 			// case the callee is a type, we perform a type conversion.
	// 			ast::NamePart::Call(ref _elems) => {
	// 				let callee_ty = self.ty(inner)?;
	// 				panic!("call to {:?} not implemented", callee_ty);
	// 				// let mut had_named = false;
	// 				// for i in 0..elems.len() {

	// 				// }
	// 			}

	// 			// Disallow `.all` in expressions.
	// 			ast::NamePart::SelectAll(span) => {
	// 				self.sess.emit(
	// 					DiagBuilder2::error("`.all` in an expression")
	// 					.span(span)
	// 				);
	// 				return Err(());
	// 			}

	// 			// Disallow ranges in expressions.
	// 			ast::NamePart::Range(ref expr) => {
	// 				self.sess.emit(
	// 					DiagBuilder2::error("range in an expression")
	// 					.span(expr.span)
	// 				);
	// 				return Err(());
	// 			}
	// 		}
	// 	}

	// 	Ok(expr)
	// }
}


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
				self.sb.hir_table.borrow_mut().set(inner, expr);

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
		Some(ast::RangeType(ref range_expr, ref _units)) => {
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

		Some(_) => unimplemented!(),
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
