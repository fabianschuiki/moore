// Copyright (c) 2017 Fabian Schuiki

//! This module implements the renumbering pass for the VHDL AST. This pass
//! allocates node IDs, builds a hierarchy of scopes, and adds a definition to
//! them for every item in the tree that can be referred to by name.

use moore_common::source::*;
use syntax::ast::{self, NodeId, def_name_from_primary_name};
use symtbl::{SymTbl, Scope, Def, DefName};


pub struct Renumberer<'ts> {
	pub symtbl: &'ts mut SymTbl,
	scope_stack: Vec<Scope>,
}

impl<'ts> Renumberer<'ts> {
	/// Create a new renumberer.
	pub fn new(symtbl: &'ts mut SymTbl) -> Renumberer<'ts> {
		Renumberer {
			symtbl: symtbl,
			scope_stack: Vec::new(),
		}
	}

	/// Allocate a new unused node ID.
	fn alloc_id(&mut self) -> NodeId {
		self.symtbl.alloc_id()
	}

	/// Push a scope for a specific node ID onto the stack. Call this before
	/// walking a node's children.
	pub fn push_scope(&mut self, node_id: NodeId) {
		let parent_id = {
			let scope = self.scope_stack.last_mut().unwrap_or(&mut self.symtbl.root_scope);
			scope.declare_subscope(node_id);
			scope.node_id
		};
		// for _ in 0..self.scope_stack.len() { print!("| "); }
		// println!("push scope {}", node_id);
		let mut scope = Scope::new(node_id);
		scope.parent_id = Some(parent_id);
		self.scope_stack.push(scope);
	}

	/// Pop a scope off the stack. Call this when done with renumbering a node's
	/// children.
	pub fn pop_scope(&mut self) {
		let scope = self.scope_stack.pop().expect("no scope on the stack");
		// for _ in 0..self.scope_stack.len() { print!("| "); }
		// println!("pop scope {}", scope.node_id);
		self.symtbl.add_scope(scope);
	}

	/// Obtain a reference to the current scope.
	pub fn scope(&self) -> &Scope {
		self.scope_stack.last().expect("no scope on the stack")
	}

	/// Obtain a mutable reference to the current scope.
	pub fn scope_mut(&mut self) -> &mut Scope {
		self.scope_stack.last_mut().expect("no scope on the stack")
	}

	/// Declare a name in the current scope.
	pub fn declare(&mut self, name: Spanned<DefName>, def: Def) {
		// for _ in 0..self.scope_stack.len() { print!("| "); }
		// println!("declare {:?} `{}`", def, name.value);
		self.scope_mut().declare(name, def);
		// If this is the design unit scope (i.e. the stack contains two scopes:
		// [library, design unit]), also declare the name in the library scope.
		// This is a hack since we want the design unit scope to contain all the
		// imported names and libraries, but have the primary or secondary unit
		// to be visible in the library. If we did not do this, e.g. entities
		// would not be visible in the library, since their declaration would
		// only be added to the design unit scope.
		if self.scope_stack.len() == 2 {
			self.scope_stack[0].declare(name, def);
		}
	}


	pub fn fold_design_unit(&mut self, mut node: ast::DesignUnit) -> ast::DesignUnit {
		use self::ast::DesignUnitData::*;
		// Allocate a node ID and a separate scope to the design unit. This is
		// where the context items will be imported to.
		node.id = self.alloc_id();
		self.push_scope(node.id);

		// Add declarations of context items.
		node.ctx = node.ctx.into_iter().map(|n|{
			match n {
				ast::CtxItem::LibClause(names) => {
					ast::CtxItem::LibClause(names.map(|n| n.into_iter().map(|mut n|{
						n.id = self.alloc_id();
						self.declare(Spanned::new(DefName::Ident(n.name), n.span), Def::Lib(n.id));
						n
					}).collect()))
				}
				other => other
			}
		}).collect();

		node.data = match node.data {
			EntityDecl(n) => EntityDecl(self.fold_entity_decl(n)),
			CfgDecl(n) => CfgDecl(self.fold_cfg_decl(n)),
			PkgDecl(n) => PkgDecl(self.fold_pkg_decl(n)),
			PkgInst(n) => PkgInst(self.fold_pkg_inst(n)),
			CtxDecl(n) => CtxDecl(self.fold_ctx_decl(n)),
			ArchBody(n) => ArchBody(self.fold_arch_body(n)),
			PkgBody(n) => PkgBody(self.fold_pkg_body(n)),
		};
		self.pop_scope();
		node
	}

	pub fn fold_entity_decl(&mut self, mut node: ast::EntityDecl) -> ast::EntityDecl {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Entity(node.id));
		self.push_scope(node.id);
		node.decls = node.decls.into_iter().map(|n| self.fold_decl_item(n)).collect();
		node.stmts = node.stmts.map(|v| v.into_iter().map(|n| self.fold_stmt(n)).collect());
		self.pop_scope();
		node
	}

	pub fn fold_cfg_decl(&mut self, mut node: ast::CfgDecl) -> ast::CfgDecl {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Cfg(node.id));
		self.push_scope(node.id);
		node.decls = node.decls.into_iter().map(|n| self.fold_decl_item(n)).collect();
		self.pop_scope();
		node
	}

	pub fn fold_pkg_decl(&mut self, mut node: ast::PkgDecl) -> ast::PkgDecl {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Pkg(node.id));
		self.push_scope(node.id);
		node.decls = node.decls.into_iter().map(|n| self.fold_decl_item(n)).collect();
		self.pop_scope();
		node
	}

	pub fn fold_pkg_inst(&mut self, mut node: ast::PkgInst) -> ast::PkgInst {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::PkgInst(node.id));
		node
	}

	pub fn fold_ctx_decl(&mut self, mut node: ast::CtxDecl) -> ast::CtxDecl {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Ctx(node.id));
		node
	}

	pub fn fold_arch_body(&mut self, mut node: ast::ArchBody) -> ast::ArchBody {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Arch(node.id));
		self.push_scope(node.id);
		node.decls = node.decls.into_iter().map(|n| self.fold_decl_item(n)).collect();
		node.stmts = node.stmts.into_iter().map(|n| self.fold_stmt(n)).collect();
		self.pop_scope();
		node
	}

	pub fn fold_pkg_body(&mut self, mut node: ast::PkgBody) -> ast::PkgBody {
		node.decls = node.decls.into_iter().map(|n| self.fold_decl_item(n)).collect();
		node
	}

	pub fn fold_decl_item(&mut self, node: ast::DeclItem) -> ast::DeclItem {
		use self::ast::DeclItem::*;
		match node {
			PkgBody(n) => PkgBody(self.fold_pkg_body(n)),
			PkgInst(n) => PkgInst(self.fold_pkg_inst(n)),
			PkgDecl(n) => PkgDecl(self.fold_pkg_decl(n)),
			TypeDecl(n) => TypeDecl(self.fold_type_decl(n)),
			SubtypeDecl(n) => SubtypeDecl(self.fold_subtype_decl(n)),
			ObjDecl(n) => ObjDecl(self.fold_obj_decl(n)),
			AliasDecl(n) => AliasDecl(self.fold_alias_decl(n)),
			UseClause(n) => UseClause(n),
			SubprogDecl(n) => SubprogDecl(self.fold_subprog_decl(n)),
			CompDecl(n) => CompDecl(self.fold_comp_decl(n)),
			DisconDecl(n) => DisconDecl(n),
			CfgSpec(n) => CfgSpec(n),
			AttrDecl(n) => AttrDecl(self.fold_attr_decl(n)),
			PortgenMap(k, n) => PortgenMap(k, n),
			PortgenClause(k, n) => PortgenClause(k, Spanned::new(n.value.into_iter().map(|i| self.fold_intf_decl(i)).collect(), n.span)),
			GroupDecl(n) => GroupDecl(self.fold_group_decl(n)),
			VunitBindInd(n) => VunitBindInd(n),
			BlockCompCfg(n) => BlockCompCfg(n),
		}
	}

	pub fn fold_type_decl(&mut self, mut node: ast::TypeDecl) -> ast::TypeDecl {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Ty(node.id));
		node
	}

	pub fn fold_subtype_decl(&mut self, mut node: ast::SubtypeDecl) -> ast::SubtypeDecl {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Subty(node.id));
		node
	}

	pub fn fold_obj_decl(&mut self, mut node: ast::ObjDecl) -> ast::ObjDecl {
		use self::ast::ObjKind::*;
		let make_def = match node.kind {
			Const => Def::Const,
			Signal => Def::Signal,
			File => Def::File,
			Var => Def::Var,
			SharedVar => Def::Var,
		};
		node.names = node.names.into_iter().map(|mut n|{
			n.id = self.alloc_id();
			self.declare(Spanned::new(DefName::Ident(n.name), n.span), make_def(n.id));
			n
		}).collect();
		node
	}

	pub fn fold_alias_decl(&mut self, mut node: ast::AliasDecl) -> ast::AliasDecl {
		node.id = self.alloc_id();
		self.declare(def_name_from_primary_name(&node.name), Def::Alias(node.id));
		node
	}

	pub fn fold_subprog_decl(&mut self, mut node: ast::Subprog) -> ast::Subprog {
		node.id = self.alloc_id();
		node.data = match node.data {
			ast::SubprogData::Decl => {
				self.declare(def_name_from_primary_name(&node.spec.name), Def::Subprog(node.id));
				ast::SubprogData::Decl
			}
			ast::SubprogData::Body{ mut decls, mut stmts } => {
				self.push_scope(node.id);
				decls = decls.into_iter().map(|n| self.fold_decl_item(n)).collect();
				stmts = stmts.into_iter().map(|n| self.fold_stmt(n)).collect();
				self.pop_scope();
				ast::SubprogData::Body{ decls: decls, stmts: stmts }
			}
			x => x
		};
		node
	}

	pub fn fold_comp_decl(&mut self, mut node: ast::CompDecl) -> ast::CompDecl {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Comp(node.id));
		node
	}

	pub fn fold_attr_decl(&mut self, mut node: ast::AttrDecl) -> ast::AttrDecl {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Attr(node.id));
		node
	}

	pub fn fold_intf_decl(&mut self, node: ast::IntfDecl) -> ast::IntfDecl {
		match node {
			ast::IntfDecl::TypeDecl(n) => ast::IntfDecl::TypeDecl(self.fold_type_decl(n)),
			ast::IntfDecl::SubprogSpec(n) => ast::IntfDecl::SubprogSpec(self.fold_intf_subprog_decl(n)),
			ast::IntfDecl::PkgInst(n) => ast::IntfDecl::PkgInst(self.fold_pkg_inst(n)),
			ast::IntfDecl::ObjDecl(n) => ast::IntfDecl::ObjDecl(self.fold_intf_obj_decl(n)),
		}
	}

	pub fn fold_intf_subprog_decl(&mut self, mut node: ast::IntfSubprogDecl) -> ast::IntfSubprogDecl {
		node.id = self.alloc_id();
		self.declare(def_name_from_primary_name(&node.spec.name), Def::Subprog(node.id));
		node
	}

	pub fn fold_intf_obj_decl(&mut self, mut node: ast::IntfObjDecl) -> ast::IntfObjDecl {
		use self::ast::IntfObjKind::*;
		let make_def = match node.kind {
			Const => Def::Const,
			Signal => Def::Signal,
			Var => Def::Var,
			File => Def::File,
		};
		node.names = node.names.into_iter().map(|mut n|{
			n.id = self.alloc_id();
			self.declare(Spanned::new(DefName::Ident(n.name), n.span), make_def(n.id));
			n
		}).collect();
		node
	}

	pub fn fold_group_decl(&mut self, mut node: ast::GroupDecl) -> ast::GroupDecl {
		node.id = self.alloc_id();
		self.declare(node.name.map(|n| DefName::Ident(n)), Def::Group(node.id));
		node
	}

	pub fn fold_stmt(&mut self, mut node: ast::Stmt) -> ast::Stmt {
		node.id = self.alloc_id();
		if let Some(label) = node.label {
			match node.data {
				_ => self.declare(label.map(|n| DefName::Ident(n)), Def::Stmt(node.id)),
			}
		}
		node.data = match node.data {
			// ast::WaitStmt has no scope
			// ast::AssertStmt has no scope
			// ast::ReportStmt has no scope
			ast::IfStmt{ conds, alt } => {
				let conds = conds.into_iter().map(|(expr, body)| (expr, self.fold_stmt_body(body))).collect();
				let alt = alt.map(|n| self.fold_stmt_body(n));
				ast::IfStmt{
					conds: conds,
					alt: alt,
				}
			}
			ast::CaseStmt{ qm, switch, cases } => {
				let cases = cases.into_iter().map(|(choices, body)| (choices, self.fold_stmt_body(body))).collect();
				ast::CaseStmt{
					qm: qm,
					switch: switch,
					cases: cases,
				}
			}
			ast::LoopStmt{ scheme, body } => {
				ast::LoopStmt{
					scheme: scheme,
					body: self.fold_stmt_body(body),
				}
			}
			// ast::NexitStmt has no scope
			// ast::ReturnStmt has no scope
			// ast::NullStmt has no scope
			ast::IfGenStmt{ conds, alt } => {
				let conds = conds.into_iter().map(|(expr, body)| (expr, self.fold_gen_body(body))).collect();
				let alt = alt.map(|n| self.fold_gen_body(n));
				ast::IfGenStmt{
					conds: conds,
					alt: alt,
				}
			}
			ast::CaseGenStmt{ switch, cases } => {
				let cases = cases.into_iter().map(|(choices, body)| (choices, self.fold_gen_body(body))).collect();
				ast::CaseGenStmt{
					switch: switch,
					cases: cases,
				}
			}
			ast::ForGenStmt{ param, range, body } => {
				ast::ForGenStmt{
					param: param,
					range: range,
					body: self.fold_gen_body(body),
				}
			}
			ast::BlockStmt{ guard, decls, stmts } => {
				let decls = decls.into_iter().map(|n| self.fold_decl_item(n)).collect();
				let stmts = stmts.into_iter().map(|n| self.fold_stmt(n)).collect();
				ast::BlockStmt{
					guard: guard,
					decls: decls,
					stmts: stmts,
				}
			}
			ast::ProcStmt{ sensitivity, decls, stmts, postponed } => {
				self.push_scope(node.id);
				let decls = decls.into_iter().map(|n| self.fold_decl_item(n)).collect();
				let stmts = stmts.into_iter().map(|n| self.fold_stmt(n)).collect();
				self.pop_scope();
				ast::ProcStmt{
					sensitivity: sensitivity,
					decls: decls,
					stmts: stmts,
					postponed: postponed,
				}
			}
			// ast::AssignStmt has no scope
			// ast::SelectAssignStmt has no scope
			// ast::InstOrCallStmt has no scope
			other => other
		};
		node
	}

	pub fn fold_stmt_body(&mut self, mut node: ast::StmtBody) -> ast::StmtBody {
		node.id = self.alloc_id();
		self.push_scope(node.id);
		node.stmts = node.stmts.into_iter().map(|n| self.fold_stmt(n)).collect();
		self.pop_scope();
		node
	}

	pub fn fold_gen_body(&mut self, mut node: ast::GenBody) -> ast::GenBody {
		node.id = self.alloc_id();
		self.push_scope(node.id);
		node.decls = node.decls.into_iter().map(|n| self.fold_decl_item(n)).collect();
		node.stmts = node.stmts.into_iter().map(|n| self.fold_stmt(n)).collect();
		self.pop_scope();
		node
	}
}
