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
		/// Literals
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
							Some(v) => hir::ExprData::IntegerLiteral(ConstInt::new(v)),
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
