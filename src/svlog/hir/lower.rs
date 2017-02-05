// Copyright (c) 2017 Fabian Schuiki

//! This module implements the process of lowering AST to HIR.

use std;
use errors::*;
use svlog::ast;
use svlog::hir::*;
use Session;

/// General result of lowering a node.
type Result<T> = std::result::Result<T, ()>;

pub fn lower(session: &Session, asts: Vec<ast::Root>) -> Result<()> {
	let mut l = Lowerer {
		session: session,
		severity: Severity::Note,
	};
	l.map_asts(asts)?;
	Err(())
}

struct Lowerer<'a> {
	session: &'a Session,
	severity: Severity,
}

impl<'a> Lowerer<'a> {
	fn add_diag(&mut self, diag: DiagBuilder2) {
		self.severity = std::cmp::max(self.severity, diag.severity);
		println!("{}", diag);
	}

	/// Lower multiple root nodes.
	fn map_asts(&mut self, asts: Vec<ast::Root>) -> Result<()> {
		for ast in asts {
			self.map_ast(ast);
		}
		Err(())
	}

	/// Lower a root node.
	fn map_ast(&mut self, ast: ast::Root) {
		for item in ast.items {
			self.map_item(item);
		}
	}

	/// Lower a root item.
	fn map_item(&mut self, node: ast::Item) {
		match node {
			ast::Item::Module(d) => self.map_module(d),
			ast::Item::Interface(d) => self.map_interface(d),
			ast::Item::Package(d) => self.map_package(d),
			ast::Item::Item(ast::HierarchyItem::ImportDecl(_)) => (), // import decls irrelevant after name resolution
			x => self.add_diag(DiagBuilder2::error(format!("{} cannot appear here", x.as_str())).span(x.span())),
		}
	}

	/// Lower a module.
	fn map_module(&mut self, node: ast::ModDecl) {
		// TODO: Digest name, lifetime, timeunits
		// TODO: Digest parameters
		// TODO: Digest ports (ANSI and non-ANSI)
	}

	/// Lower an interface.
	fn map_interface(&mut self, node: ast::IntfDecl) {

	}

	/// Lower a package.
	fn map_package(&mut self, node: ast::PackageDecl) {

	}
}
