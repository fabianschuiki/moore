// Copyright (c) 2018 Fabian Schuiki

//! Sequential statements

#![deny(missing_docs)]

use add_ctx::AddContext;
use syntax::ast;
use hir;
use score::*;

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> AddContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
	/// Add a wait statement.
	pub fn add_wait_stmt(&self, stmt: &'ast ast::Stmt) -> WaitStmtRef {
		let mk = self.make(stmt.span);
		mk.finish()
	}
}
