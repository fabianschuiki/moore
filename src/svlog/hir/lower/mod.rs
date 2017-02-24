// Copyright (c) 2017 Fabian Schuiki

//! This module implements the process of lowering AST to HIR.

mod port;

use std;
use moore_common::errors::*;
use moore_common::Session;
use moore_svlog_syntax::ast;
use moore_svlog_syntax::resolve::NameResolution;
use nodes::*;
use std::collections::HashMap;

/// General result of lowering a node.
type Result<T> = std::result::Result<T, ()>;

pub fn lower(session: &Session, nameres: &NameResolution, top: NodeId, asts: Vec<ast::Root>) -> Result<Root> {
	let mut l = Lowerer {
		session: session,
		nameres: nameres,
		severity: Severity::Note,
		top: top,
		mods: HashMap::new(),
	};
	l.map_asts(asts);
	l.finish()
}

#[allow(dead_code)]
struct Lowerer<'a> {
	session: &'a Session,
	nameres: &'a NameResolution,
	severity: Severity,
	top: NodeId,
	mods: HashMap<NodeId, Module>,
}

impl<'a> Lowerer<'a> {
	fn add_diag(&mut self, diag: DiagBuilder2) {
		self.severity = std::cmp::max(self.severity, diag.severity);
		println!("{}", diag);
	}

	fn is_error(&self) -> bool {
		self.severity >= Severity::Error
	}

	/// Consume the lowerer and wrap the lowered nodes up in a Root node.
	fn finish(self) -> Result<Root> {
		if self.severity >= Severity::Error {
			Err(())
		} else {
			Ok(Root {
				top: self.top,
				mods: self.mods,
				intfs: HashMap::new(),
				pkgs: HashMap::new(),
			})
		}
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
		println!("mapping module {}", node.name);

		// If the first port has neither direction, port kind, nor type
		// specified, non-ANSI style shall be assumed. Otherwise, the ports are
		// assumed to be in ANSI style.
		let ports = match self.map_ports(node.ports, &node.items) {
			Ok(x) => x,
			Err(()) => return,
		};

		// TODO: Digest name, lifetime, timeunits
		// TODO: Digest parameters
		let m = Module {
			name: node.name,
			span: node.name_span,
			ports: ports,
		};

		// Stash the module away in the modules map, associated with its node
		// ID.
		if let Some(e) = self.mods.insert(node.id, m) {
			panic!("modules `{}` and `{}` both have ID {}", e.name, node.name, node.id);
		}
	}

	/// Lower an interface.
	fn map_interface(&mut self, node: ast::IntfDecl) {

	}

	/// Lower a package.
	fn map_package(&mut self, node: ast::PackageDecl) {

	}
}


/// Check if a type is empty, i.e. it is an implicit type with no sign or packed
/// dimensions specified.
fn is_type_empty(ty: &ast::Type) -> bool {
	ty.data == ast::ImplicitType && ty.sign == ast::TypeSign::None && ty.dims.is_empty()
}
