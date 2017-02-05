// Copyright (c) 2017 Fabian Schuiki

//! This module implements the process of lowering AST to HIR.

use std;
use moore_common::errors::*;
use moore_common::Session;
use ast;
use hir::*;
use resolve::NameResolution;
use std::collections::HashMap;

/// General result of lowering a node.
type Result<T> = std::result::Result<T, ()>;

pub fn lower(session: &Session, nameres: &NameResolution, top: NodeId, asts: Vec<ast::Root>) -> Result<Root> {
	let mut l = Lowerer {
		session: session,
		severity: Severity::Note,
		top: top,
	};
	l.map_asts(asts);
	l.finish()
}

struct Lowerer<'a> {
	session: &'a Session,
	severity: Severity,
	top: NodeId,
}

impl<'a> Lowerer<'a> {
	fn add_diag(&mut self, diag: DiagBuilder2) {
		self.severity = std::cmp::max(self.severity, diag.severity);
		println!("{}", diag);
	}

	/// Consume the lowerer and wrap the lowered nodes up in a Root node.
	fn finish(self) -> Result<Root> {
		Ok(Root {
			top: self.top,
			mods: HashMap::new(),
			intfs: HashMap::new(),
			pkgs: HashMap::new(),
		})
	}

	/// Lower multiple root nodes.
	fn map_asts(&mut self, asts: Vec<ast::Root>) {
		for ast in asts {
			self.map_ast(ast);
		}
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
