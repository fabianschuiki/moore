// Copyright (c) 2017 Fabian Schuiki

//! This module implements lowering of the AST to the HIR.

use score::*;


impl<'sb, 'ast, 'ctx> ScoreContext<'sb, 'ast, 'ctx> {
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
