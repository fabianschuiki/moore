// Copyright (c) 2017 Fabian Schuiki

//! This module provides name resolution for ASTs. The targeted approach is as
//! follows:
//!
//! 1. Perform a first pass where names are collected and scopes are assembled.
//!    Scopes shall be collected into a scope map, indexed by the item ID.
//! 2. Perform a second pass where names are resolved against the ones collected
//!    in step 1. This should then allow for proper resolution of imports,
//!    hierarchical names, and paths (`pkg::name` and `intf.modport`).
//!
//! # Todo
//!
//! Implement a more efficient way of resolving names. In a first pass, iterate
//! over all globally visible items, and items that are accessible through
//! hierarchical names, and store them in a lookup table. Then perform a second
//! pass where we go through each and every item in the AST and resolve names.
//! In this second pass we keep a stack of local scopes that we use to resolve
//! variable names and other local declarations. Whenever we cannot find
//! something, we resolve to checking the lookup table discussed above. Be wary
//! of the precedence between the lookup table and the individual local scopes.

use std;
use super::ast::{self, NodeId};
use moore_common::name::*;
use moore_common::source::*;
use moore_common::errors::*;
use moore_common::Session;
use std::collections::{HashMap, HashSet};


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefId {
	Error,
	Module(NodeId),
	Interface(NodeId),
	Package(NodeId),
	Port(NodeId),
	Var(NodeId),
	Param(NodeId),
	Modport(NodeId),
	Subroutine(NodeId),
	Typedef(NodeId),
	Class(NodeId),
	Inst(NodeId),
}

impl DefId {
	pub fn is_error(&self) -> bool {
		match *self {
			DefId::Error => true,
			_ => false,
		}
	}

	pub fn node_id(&self) -> NodeId {
		match *self {
			DefId::Error => panic!("trying to access a node id on a DefId::Error"),
			DefId::Module(id) |
			DefId::Interface(id) |
			DefId::Package(id) |
			DefId::Port(id) |
			DefId::Var(id) |
			DefId::Param(id) |
			DefId::Modport(id) |
			DefId::Subroutine(id) |
			DefId::Typedef(id) |
			DefId::Class(id) |
			DefId::Inst(id) => id
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Def {
	pub span: Span,
	pub id: DefId,
}


pub fn resolve(session: &Session, asts: &[ast::Root]) -> Result<NameResolution, ()> {
	let mut r = Resolver::new(session);
	r.register_globals(asts);
	if r.is_error() {
		return Err(());
	}
	r.scopes.push(Scope::new_local());
	for ast in asts {
		r.resolve_ast(ast);
	}
	r.scopes.pop().unwrap();
	r.finish()
}

/// The result of name resolution: An association between every identifier in
/// the AST and a definition it points to.
pub type NameResolution = HashMap<NodeId, NodeId>;

/// The struct used to resolve names. This is a temporary construct that is only
/// used to contain the session, symbol table, and the resulting name table.
/// Is finally turned into a NameResolution that only contains the result.
struct Resolver<'a> {
	session: &'a Session,
	severity: Severity,
	scopes: Vec<Scope<'a>>,
	defs: HashMap<NodeId, DefId>,
	intf_map: HashMap<NodeId, &'a ast::IntfDecl>,
	pkg_map: HashMap<NodeId, &'a ast::PackageDecl>,
	mod_map: HashMap<NodeId, &'a ast::ModDecl>,
}

// TODO: Make this into a ScopeKind enum. Then add a Scope struct that has a
// kind, but also contains a lookup cache table for speed. Then extend the
// resolver to provide a function that pushes a scope onto and pops it off the
// stack again, calling a lambda in between.
#[derive(Debug)]
enum Scope<'a> {
	Global(HashMap<Name, Def>),
	Module(&'a ast::ModDecl),
	Interface(&'a ast::IntfDecl),
	Package(&'a ast::PackageDecl),
	Local {
		defs: HashMap<Name, Def>,
		imported: Vec<Scope<'a>>,
	},
}

impl<'a> Scope<'a> {
	pub fn new_local() -> Scope<'a> {
		Scope::Local {
			defs: HashMap::new(),
			imported: Vec::new(),
		}
	}
}

macro_rules! assert_renumbered {
	($span:expr, $id:expr) => {
		if $id == ast::DUMMY_NODE_ID {
			panic!("{}", DiagBuilder2::fatal("node id has been missed during renumbering").span($span));
		}
	}
}

impl<'a> Resolver<'a> {
	pub fn new(session: &'a Session) -> Resolver<'a> {
		Resolver {
			session: session,
			severity: Severity::Note,
			scopes: Vec::new(),
			defs: HashMap::new(),
			intf_map: HashMap::new(),
			pkg_map: HashMap::new(),
			mod_map: HashMap::new(),
		}
	}

	pub fn is_error(&self) -> bool {
		self.severity >= Severity::Error
	}

	/// Issues a diagnostic message.
	fn add_diag(&mut self, diag: DiagBuilder2) {
		self.severity = std::cmp::max(self.severity, diag.severity);
		println!("{}", diag);
	}

	/// Finish resolution and wrap the Resolver up into a NameResolution. Fails
	/// if an error occurred during resolution.
	pub fn finish(self) -> Result<NameResolution, ()> {
		if self.severity >= Severity::Error {
			Err(())
		} else {
			Ok(self.defs.iter().map(|(k, def)| (*k, def.node_id())).collect())
		}
	}

	pub fn register_globals(&mut self, asts: &'a [ast::Root]) {
		let mut tbl = HashMap::new();
		for ast in asts {
			for item in &ast.items {
				let (name, span, defid) = match *item {
					ast::Item::Module(ref decl) => {
						self.mod_map.insert(decl.id, decl);
						(decl.name, decl.name_span, DefId::Module(decl.id))
					},
					ast::Item::Interface(ref decl) => {
						self.intf_map.insert(decl.id, decl);
						(decl.name, decl.name_span, DefId::Interface(decl.id))
					},
					ast::Item::Package(ref decl) => {
						self.pkg_map.insert(decl.id, decl);
						(decl.name, decl.name_span, DefId::Package(decl.id))
					},
					_ => continue
				};

				// Wrap the DefId together with a span up in a Def struct and
				// insert that into the global name table. If we find an
				// existing definition, throw an error or warning.
				if let Some(ex) = tbl.insert(name, Def { span: span, id: defid }) {
					if ex.span != span && !self.session.opts.ignore_duplicate_defs {
						self.add_diag(DiagBuilder2::error(format!("`{}` has already been declared", name))
							.span(span)
							.add_note("pass --ignore-duplicate-defs to use the last definition and suppress this error")
							.add_note("previous declaration was here")
							.span(ex.span));
					}
				}
			}
		}

		// Move the declarations we found into the global scope.
		self.scopes.push(Scope::Global(tbl));
	}

	pub fn resolve_ast(&mut self, ast: &'a ast::Root) {
		for item in &ast.items {
			self.resolve_item(item);
		}
	}

	pub fn resolve_item(&mut self, item: &'a ast::Item) {
		match *item {
			ast::Item::Module(ref decl) => {
				self.scopes.push(Scope::Module(decl));
				self.scopes.push(Scope::new_local());
				self.resolve_param_ports(&decl.params);
				self.resolve_ports(&decl.ports);
				self.resolve_hierarchy_items(&decl.items);
				self.scopes.pop().unwrap();
				self.scopes.pop().unwrap();
			}
			ast::Item::Interface(ref decl) => {
				self.scopes.push(Scope::Interface(decl));
				self.scopes.push(Scope::new_local());
				self.resolve_param_ports(&decl.params);
				self.resolve_ports(&decl.ports);
				self.resolve_hierarchy_items(&decl.items);
				self.scopes.pop().unwrap();
				self.scopes.pop().unwrap();
			}
			ast::Item::Package(ref decl) => self.resolve_hierarchy_items(&decl.items),
			ast::Item::Item(ref item) => self.resolve_hierarchy_item(item),
		}
	}

	pub fn resolve_param_ports(&mut self, params: &[ast::ParamDecl]) {
		for param in params {
			self.resolve_param_port(param);
		}
	}

	pub fn resolve_param_port(&mut self, param: &ast::ParamDecl) {
		// TODO: Maybe register the parameter here in a local scope, such that
		// other parameters in the parameter port list can refer to it?
		self.resolve_param_decl(param);
		// self.resolve_dims(&param.dims);
		// if let Some(ref e) = param.expr {
		// 	self.resolve_expr(e);
		// }
	}

	pub fn resolve_ports(&mut self, ports: &[ast::Port]) {
		for port in ports {
			self.resolve_port(port);
		}
	}

	pub fn resolve_port(&mut self, port: &ast::Port) {
		match *port {
			ast::Port::Intf { ref dims, ref expr, .. } => {
				self.resolve_dims(dims);
				if let Some(ref expr) = *expr {
					self.resolve_expr(expr);
				}
			}

			ast::Port::Explicit { ref expr, .. } => {
				if let Some(ref expr) = *expr {
					self.resolve_expr(expr);
				}
			}

			ast::Port::Named { ref ty, ref dims, ref expr, .. } => {
				self.resolve_type(ty);
				self.resolve_dims(dims);
				if let Some(ref expr) = *expr {
					self.resolve_expr(expr);
				}
			}

			ast::Port::Implicit(ref expr) => self.resolve_expr(expr),
		}
	}

	pub fn resolve_type(&mut self, ty: &ast::Type) {
		match ty.data {
			ast::NamedType(ref name) => {
				self.resolve_ident(name);
				// self.add_diag(DiagBuilder2::error("don't know how to resolve named types").span(ty.span));
			}

			ast::ScopedType{ty: ref super_ty, ref name, member, ..} => {
				self.resolve_type(super_ty);
				if member {
					// Try to resolve the modport. This is very convoluted as of
					// now.
					// TODO: Clean this up later.
					if let ast::NamedType(ref super_name) = super_ty.data {
						if let Some(&DefId::Interface(id)) = self.defs.get(&super_name.id) {
							if let Some(def) = search_modport_decl(&self.intf_map.get(&id).expect("interface missing from intf_map").items, name.name) {
								self.bind(name, def);
							} else {
								self.add_diag(DiagBuilder2::error(format!("`{}` is not a modport declared in interface `{}`", name.name, super_name.name)).span(name.span));
							}
						} else {
							self.add_diag(DiagBuilder2::error(format!("`{}` is not an interface; cannot access modport `{}` on non-interface", super_name.name, name.name)).span(super_ty.span));
						}
					} else {
						self.add_diag(DiagBuilder2::error(format!("cannot access modport `{}` on non-interface", name.name)).span(super_ty.span));
					}
				} else {
					self.add_diag(DiagBuilder2::error("don't know how to resolve namespaced types").span(ty.span));
				}
			}

			ast::EnumType(ref inner, ref names) => {
				// self.add_diag(DiagBuilder2::note("resolving enum type").span(ty.span));
				if let Some(ref i) = *inner {
					self.resolve_type(i);
				}
				for name in names {
					assert_renumbered!(name.name.span, name.name.id);
					self.define(name.name.name, name.name.span, DefId::Var(name.name.id));
					if let Some(ref e) = name.range {
						self.resolve_expr(e);
					}
					if let Some(ref e) = name.value {
						self.resolve_expr(e);
					}
				}
			}

			ast::StructType{ref members, ..} => for member in members {
				self.resolve_type(&member.ty);
				for name in &member.names {
					self.resolve_dims(&name.dims);
					if let Some(ref i) = name.init {
						self.resolve_expr(i);
					}
				}
			},

			ast::SpecializedType(ref ty, ref params) => {
				self.resolve_type(ty);
				// TODO: Resolve parameter assignments.
			}

			// Trivial cases.
			ast::ImplicitType |
			ast::VoidType |
			ast::StringType |
			ast::ChandleType |
			ast::VirtIntfType(_) |
			ast::EventType |
			ast::MailboxType |
			ast::BitType |
			ast::LogicType |
			ast::RegType |
			ast::ByteType |
			ast::ShortIntType |
			ast::IntType |
			ast::LongIntType |
			ast::TimeType |
			ast::ShortRealType |
			ast::RealType |
			ast::RealtimeType => ()
		}
		self.resolve_dims(&ty.dims);
	}

	pub fn resolve_dims(&mut self, dims: &[ast::TypeDim]) {
		for dim in dims {
			self.resolve_dim(dim);
		}
	}

	pub fn resolve_dim(&mut self, dim: &ast::TypeDim) {
		match *dim {
			ast::TypeDim::Expr(ref e) => self.resolve_expr(e),
			ast::TypeDim::Range(ref a, ref b) => {
				self.resolve_expr(a);
				self.resolve_expr(b);
			}
			ast::TypeDim::Queue |
			ast::TypeDim::Unsized |
			ast::TypeDim::Associative => unimplemented!(),
		}
	}

	pub fn resolve_hierarchy_items(&mut self, items: &[ast::HierarchyItem]) {
		for item in items {
			self.resolve_hierarchy_item(item);
		}
	}

	pub fn resolve_hierarchy_item(&mut self, item: &ast::HierarchyItem) {
		match *item {
			ast::HierarchyItem::Procedure(ref prc) => self.resolve_procedure(prc),
			ast::HierarchyItem::VarDecl(ref decl) => self.resolve_var_decl(decl, false),
			ast::HierarchyItem::ParamDecl(ref decl) => self.resolve_param_decl(decl),
			ast::HierarchyItem::ImportDecl(ref decl) => self.resolve_import_decl(decl),
			ast::HierarchyItem::SubroutineDecl(ref decl) => self.resolve_subroutine_decl(decl),
			ast::HierarchyItem::ContAssign(ref assign) => {
				if let Some(ref delay) = assign.delay {
					self.resolve_expr(delay);
				}
				if let Some(ref dc) = assign.delay_control {
					self.resolve_expr(&dc.expr);
				}
				for &(ref lhs, ref rhs) in &assign.assignments {
					self.resolve_expr(lhs);
					self.resolve_expr(rhs);
				}
			}
			ast::HierarchyItem::Inst(ref node) => {
				self.resolve_ident(&node.target);
				for p in &node.params {
					self.resolve_param_assignment(p);
				}
				for n in &node.names {
					self.resolve_dims(&n.dims);
					for c in &n.conns {
						self.resolve_port_conn(c);
					}
				}
			}

			// TODO: Implement the missing items.
			_ => ()
		}
	}

	pub fn resolve_param_assignment(&mut self, node: &ast::ParamAssignment) {
		self.resolve_expr(&node.expr);
	}

	pub fn resolve_port_conn(&mut self, node: &ast::PortConn) {
		match node.kind {
			ast::PortConnKind::Auto => (),
			ast::PortConnKind::Named(_, ref mode) => match *mode {
				ast::PortConnMode::Connected(ref expr) => self.resolve_expr(expr),
				ast::PortConnMode::Auto |
				ast::PortConnMode::Unconnected => (),
			},
			ast::PortConnKind::Positional(ref expr) => self.resolve_expr(expr),
		}
	}

	pub fn resolve_procedure(&mut self, prc: &ast::Procedure) {
		self.resolve_stmt(&prc.stmt);
	}

	pub fn resolve_stmts(&mut self, stmts: &[ast::Stmt]) {
		for stmt in stmts {
			self.resolve_stmt(stmt);
		}
	}

	pub fn resolve_stmt(&mut self, stmt: &ast::Stmt) {
		match stmt.data {
			ast::SequentialBlock(ref stmts) => {
				// TODO: Push a scope for the block onto the stack.
				self.scopes.push(Scope::new_local());
				self.resolve_stmts(stmts);
				self.scopes.pop().unwrap();
			},
			ast::ParallelBlock(ref stmts, _) => {
				self.scopes.push(Scope::new_local());
				self.resolve_stmts(stmts);
				self.scopes.pop().unwrap();
			}
			ast::IfStmt{ref cond, ref main_stmt, ref else_stmt, ..} => {
				self.resolve_expr(cond);
				self.resolve_stmt(main_stmt);
				if let Some(ref s) = *else_stmt {
					self.resolve_stmt(s);
				}
			}
			ast::BlockingAssignStmt{ref lhs, ref rhs, ..} => {
				self.resolve_expr(lhs);
				self.resolve_expr(rhs);
			}
			ast::NonblockingAssignStmt{ref lhs, ref rhs, ref delay, ref event} => {
				self.resolve_expr(lhs);
				if let Some(ref dc) = *delay {
					self.resolve_expr(&dc.expr);
				}
				if let Some(ref ec) = *event {
					// self.resolve_event_control(ec);
				}
				self.resolve_expr(rhs);
			}
			ast::TimedStmt(ref timing, ref stmt) => {
				self.resolve_timing_control(timing);
				self.resolve_stmt(stmt);
			}
			ast::CaseStmt{ref expr, ref items, ..} => {
				self.resolve_expr(expr);
				for item in items {
					match *item {
						ast::CaseItem::Default(ref stmt) => self.resolve_stmt(stmt),
						ast::CaseItem::Expr(ref exprs, ref stmt) => {
							for expr in exprs {
								self.resolve_expr(expr);
							}
							self.resolve_stmt(stmt);
						}
					}
				}
			}
			ast::ForeverStmt(ref stmt) => self.resolve_stmt(stmt),
			ast::RepeatStmt(ref expr, ref stmt) |
			ast::WhileStmt(ref expr, ref stmt) |
			ast::WaitExprStmt(ref expr, ref stmt) => {
				self.scopes.push(Scope::new_local());
				self.resolve_expr(expr);
				self.resolve_stmt(stmt);
				self.scopes.pop().unwrap();
			}
			ast::DoStmt(ref stmt, ref expr) => {
				self.scopes.push(Scope::new_local());
				self.resolve_stmt(stmt);
				self.resolve_expr(expr);
				self.scopes.pop().unwrap();
			}
			ast::ForStmt(ref init, ref cond, ref step, ref stmt) => {
				self.scopes.push(Scope::new_local());
				self.resolve_stmt(init);
				self.resolve_expr(cond);
				self.resolve_expr(step);
				self.resolve_stmt(stmt);
				self.scopes.pop().unwrap();
			}
			ast::ForeachStmt(ref expr, ref vars, ref stmt) => {
				self.scopes.push(Scope::new_local());
				self.resolve_expr(expr);
				for var in vars {
					if let Some(ref ident) = *var {
						self.define(ident.name, ident.span, DefId::Var(ident.id));
					}
				}
				self.scopes.pop().unwrap();
			}
			ast::ExprStmt(ref expr) => self.resolve_expr(expr),
			ast::ReturnStmt(ref expr) => if let Some(ref e) = *expr { self.resolve_expr(e); },
			ast::ImportStmt(ref decl) => self.resolve_import_decl(decl),
			ast::AssertionStmt(ref assertion) => self.resolve_assertion(assertion),
			ast::DisableStmt(name) => {
				self.add_diag(DiagBuilder2::error("Don't know how to resolve name of disabled statement").span(stmt.span));
			}
			ast::VarDeclStmt(ref decl) => self.resolve_var_decl(decl, true),

			// Trivial cases
			ast::NullStmt |
			ast::ContinueStmt |
			ast::BreakStmt |
			ast::WaitForkStmt |
			ast::DisableForkStmt => (),

			// Unimplemented cases
			ast::GenvarDeclStmt(_) => self.add_diag(DiagBuilder2::error("resolve_stmt not implemented").span(stmt.span)),
		}
	}

	pub fn resolve_expr(&mut self, expr: &ast::Expr) {
		match expr.data {
			ast::IdentExpr(ref ident) => {
				assert_renumbered!(ident.span, ident.id);
				self.resolve_ident(ident);
			}
			ast::SysIdentExpr(ref ident) => {
				assert_renumbered!(ident.span, ident.id);
				// TODO: Resolve the identifier against a table of builtin
				// system tasks, functions, and names. No need to walk the scope
				// hierarchy.
			}
			ast::IndexExpr{ref indexee, ref index, ..} => {
				self.resolve_expr(indexee);
				self.resolve_expr(index);
			}
			ast::UnaryExpr{ref expr, ..} => self.resolve_expr(expr),
			ast::BinaryExpr{ref lhs, ref rhs, ..} |
			ast::RangeExpr{ref lhs, ref rhs, ..} |
			ast::AssignExpr{ref lhs, ref rhs, ..} => {
				self.resolve_expr(lhs);
				self.resolve_expr(rhs);
			}
			ast::TernaryExpr{ref cond, ref true_expr, ref false_expr, ..} => {
				self.resolve_expr(cond);
				self.resolve_expr(true_expr);
				self.resolve_expr(false_expr);
			}
			ast::CallExpr(ref expr, ref args) => {
				self.resolve_expr(expr);
				self.resolve_call_args(args);
			}
			ast::ConstructorCallExpr(ref args) => {
				self.resolve_call_args(args);
			}
			ast::ClassNewExpr(ref expr) => if let Some(ref e) = *expr { self.resolve_expr(e); },
			ast::ArrayNewExpr(ref expr, ref other) => {
				self.resolve_expr(expr);
				if let Some(ref e) = *other {
					self.resolve_expr(e);
				}
			}
			ast::StreamConcatExpr{ref slice, ref exprs} => {
				match *slice {
					Some(ast::StreamConcatSlice::Expr(ref expr)) => self.resolve_expr(expr),
					Some(ast::StreamConcatSlice::Type(ref ty)) => self.resolve_type(ty),
					None => (),
				}
				for expr in exprs {
					self.resolve_expr(&expr.expr);
					if let Some(ref e) = expr.range {
						self.resolve_expr(e);
					}
				}
			}
			ast::ConcatExpr{ref repeat, ref exprs} => {
				if let Some(ref r) = *repeat {
					self.resolve_expr(r);
				}
				for expr in exprs {
					self.resolve_expr(expr);
				}
			}
			ast::MinTypMaxExpr{ref min, ref typ, ref max} => {
				self.resolve_expr(min);
				self.resolve_expr(typ);
				self.resolve_expr(max);
			}
			ast::MemberExpr{ref expr, ..} => self.resolve_expr(expr),
			ast::PatternExpr(ref fields) => for field in fields {
				match field.data {
					ast::PatternFieldData::Expr(ref expr) |
					ast::PatternFieldData::Default(ref expr) => self.resolve_expr(expr),
					ast::PatternFieldData::Member(ref a, ref b) => {
						self.resolve_expr(a);
						self.resolve_expr(b);
					}
					ast::PatternFieldData::Type(ref ty, ref expr) => {
						self.resolve_type(ty);
						self.resolve_expr(expr);
					}
					ast::PatternFieldData::Repeat(ref expr, ref exprs) => {
						self.resolve_expr(expr);
						for expr in exprs {
							self.resolve_expr(expr);
						}
					}
				}
			},

			// Trivial cases
			ast::LiteralExpr(_) |
			ast::EmptyQueueExpr => (),

			// Unsupported cases
			ast::DummyExpr => self.add_diag(DiagBuilder2::error("found dummy expression during resolution").span(expr.span)),
			ast::TypeExpr(_) => self.add_diag(DiagBuilder2::error("found type expression during resolution").span(expr.span)),
		}
	}

	pub fn resolve_timing_control(&mut self, tc: &ast::TimingControl) {
		match *tc {
			ast::TimingControl::Delay(ref dc) => self.resolve_expr(&dc.expr),
			ast::TimingControl::Event(ref ec) => self.resolve_event_control(ec),
			ast::TimingControl::Cycle(ref cd) => self.resolve_cycle_delay(cd),
		}
	}

	pub fn resolve_event_control(&mut self, ec: &ast::EventControl) {
		match ec.data {
			ast::EventControlData::Implicit => (),
			ast::EventControlData::Expr(ref expr) => self.resolve_event_expr(expr),
		}
	}

	pub fn resolve_cycle_delay(&mut self, cd: &ast::CycleDelay) {
	}

	pub fn resolve_import_decl(&mut self, decl: &ast::ImportDecl) {
		for item in &decl.items {
			let def = match self.resolve_ident(&item.pkg) {
				Some(d) => d,
				None => continue,
			};
			if let Some(ref name) = item.name {
				// TODO: We need to be able to resolve names in different
				// contexts. Here it would be nice to resolve names within the
				// package body.
				// TODO: Add the name to the definitions of the current scope.
				self.add_diag(DiagBuilder2::error("don't know how to handle named imports").span(decl.span));
			} else {
				match self.scopes.last_mut() {
					Some(&mut Scope::Local{ref mut imported, ..}) => {
						match def.id {
							DefId::Package(id) => imported.push(Scope::Package(self.pkg_map[&id])),
							_ => ()
						}
					}
					_ => (),
				}
			}
		}
	}

	pub fn resolve_assertion(&mut self, assertion: &ast::Assertion) {
		// TODO: Do something with the assertion label.
		match assertion.data {
			ast::AssertionData::Immediate(ref blk) |
			ast::AssertionData::Deferred(ref blk) => self.resolve_blocking_assertion(blk),
			ast::AssertionData::Concurrent(ref conc) => self.resolve_concurrent_assertion(conc),
		}
	}

	pub fn resolve_blocking_assertion(&mut self, assertion: &ast::BlockingAssertion) {
		match *assertion {
			ast::BlockingAssertion::Assert(ref expr, ref action) |
			ast::BlockingAssertion::Assume(ref expr, ref action) => {
				self.resolve_expr(expr);
				self.resolve_assertion_action_block(action);
			},
			ast::BlockingAssertion::Cover(ref expr, ref stmt) => {
				self.resolve_expr(expr);
				self.resolve_stmt(stmt);
			}
		}
	}

	pub fn resolve_concurrent_assertion(&mut self, assertion: &ast::ConcurrentAssertion) {
		match *assertion {
			ast::ConcurrentAssertion::AssertProperty(ref ps, ref action) |
			ast::ConcurrentAssertion::AssumeProperty(ref ps, ref action) |
			ast::ConcurrentAssertion::ExpectProperty(ref ps, ref action) => {
				self.resolve_propspec(ps);
				self.resolve_assertion_action_block(action);
			}
			ast::ConcurrentAssertion::CoverProperty(ref ps, ref stmt) => {
				self.resolve_propspec(ps);
				self.resolve_stmt(stmt);
			}
			ast::ConcurrentAssertion::CoverSequence => (),
			ast::ConcurrentAssertion::RestrictProperty(ref ps) => self.resolve_propspec(ps),
		}
	}

	pub fn resolve_propspec(&mut self, ps: &ast::PropSpec) {
		unimplemented!();
	}

	pub fn resolve_assertion_action_block(&mut self, action: &ast::AssertionActionBlock) {
		match *action {
			ast::AssertionActionBlock::Positive(ref stmt) |
			ast::AssertionActionBlock::Negative(ref stmt) => self.resolve_stmt(stmt),
			ast::AssertionActionBlock::Both(ref a, ref b) => {
				self.resolve_stmt(a);
				self.resolve_stmt(b);
			}
		}
	}

	pub fn resolve_event_expr(&mut self, expr: &ast::EventExpr) {
		match *expr {
			ast::EventExpr::Edge{ref value, ..} => self.resolve_expr(value),
			ast::EventExpr::Iff{ref expr, ref cond, ..} => {
				self.resolve_event_expr(expr);
				self.resolve_expr(cond);
			}
			ast::EventExpr::Or{ref lhs, ref rhs, ..} => {
				self.resolve_event_expr(lhs);
				self.resolve_event_expr(rhs);
			}
		}
	}

	pub fn resolve_call_args(&mut self, args: &[ast::CallArg]) {
		for arg in args {
			if let Some(ref e) = arg.expr {
				self.resolve_expr(e);
			}
		}
	}

	pub fn resolve_var_decl(&mut self, decl: &ast::VarDecl, define: bool) {
		self.resolve_type(&decl.ty);
		for name in &decl.names {
			assert_renumbered!(name.span, name.id);
			if define {
				self.define(name.name, name.span, DefId::Var(name.id));
			}
			self.resolve_dims(&name.dims);
			if let Some(ref i) = name.init {
				self.resolve_expr(i);
			}
		}
	}

	pub fn resolve_param_decl(&mut self, node: &ast::ParamDecl) {
		match node.kind {
			ast::ParamKind::Type(ref decls) => for decl in decls {
				if let Some(ref ty) = decl.ty {
					self.resolve_type(ty);
				}
			},
			ast::ParamKind::Value(ref decls) => for decl in decls {
				self.resolve_type(&decl.ty);
				self.resolve_dims(&decl.dims);
				if let Some(ref expr) = decl.expr {
					self.resolve_expr(expr);
				}
			},
		}
	}

	pub fn resolve_subroutine_decl(&mut self, decl: &ast::SubroutineDecl) {
		for arg in &decl.prototype.args {
			self.resolve_type(&arg.ty);
			if let Some(ref name) = arg.name {
				self.resolve_dims(&name.dims);
				if let Some(ref expr) = name.expr {
					self.resolve_expr(expr);
				}
			}
		}
		// TODO: Resolve items.
	}

	pub fn resolve_ident(&mut self, ident: &ast::Identifier) -> Option<Def> {
		if let Some(def) = self.find_def(ident.name) {
			self.bind(ident, def);
			Some(def)
		} else {
			self.add_diag(DiagBuilder2::error(format!("`{}` has not been defined", ident.name)).span(ident.span));
			None
		}
	}

	pub fn bind(&mut self, ident: &ast::Identifier, def: Def) {
		assert_renumbered!(ident.span, ident.id);
		// self.add_diag(DiagBuilder2::note(format!("`{}` bound", ident.name)).span(ident.span).add_note(format!("definition is `{:?}`", def.id)).span(def.span));
		if let Some(ex) = self.defs.insert(ident.id, def.id) {
			panic!("second resolution of `{}` (id {}): first def {:?}, second def {:?}", ident.name, ident.id, ex, def.id);
		}
	}

	pub fn find_def(&mut self, name: Name) -> Option<Def> {
		for scope in self.scopes.iter_mut().rev() {
			let def = scope.find_def(name);
			if def.is_some() {
				return def;
			}
		}
		None
	}

	pub fn define(&mut self, name: Name, span: Span, defid: DefId) {
		let prev = match self.scopes.last_mut() {
			Some(&mut Scope::Local{ref mut defs, ..}) => defs.insert(name, Def { span: span, id: defid }),
			x => panic!("tried to define {} as {:?} in incompatible scope {:?}", name, defid, x)
		};
		if let Some(p) = prev {
			self.add_diag(DiagBuilder2::error(format!("`{}` has already been declared", name)).span(span).add_note("previous declaration was here:").span(p.span));
		}
	}
}



impl<'a> Scope<'a> {
	pub fn find_def(&self, name: Name) -> Option<Def> {
		match *self {
			Scope::Local{ref defs, ref imported} => {
				if let Some(def) = defs.get(&name) {
					return Some(*def);
				}
				for scope in imported.iter().rev() {
					if let Some(def) = scope.find_def(name) {
						return Some(def);
					}
				}
				return None;
			},
			Scope::Module(decl) => search_param_ports(&decl.params, name)
				.or_else(|| search_ports(&decl.ports, name))
				.or_else(|| search_hierarchy_items(&decl.items, name)),
			Scope::Interface(decl) => search_param_ports(&decl.params, name)
				.or_else(|| search_ports(&decl.ports, name))
				.or_else(|| search_hierarchy_items(&decl.items, name)),
			Scope::Package(decl) => search_hierarchy_items(&decl.items, name),
			Scope::Global(ref defs) => defs.get(&name).map(|x| x.clone()),
		}
	}
}

fn search_param_ports(params: &[ast::ParamDecl], name: Name) -> Option<Def> {
	for param in params {
		match param.kind {
			ast::ParamKind::Type(ref decls) => for decl in decls {
				if decl.name.name == name {
					return Some(Def {
						span: decl.name.span,
						id: DefId::Param(decl.name.id),
					});
				}
			},
			ast::ParamKind::Value(ref decls) => for decl in decls {
				if decl.name.name == name {
					return Some(Def {
						span: decl.name.span,
						id: DefId::Param(decl.name.id),
					});
				}
			},
		}
	}
	None
}

fn search_ports(ports: &[ast::Port], query: Name) -> Option<Def> {
	for port in ports {
		match *port {
			ast::Port::Intf{ ref name, .. } |
			ast::Port::Explicit{ ref name, .. } |
			ast::Port::Named{ ref name, .. } => {
				if name.name == query {
					assert_renumbered!(name.span, name.id);
					return Some(Def {
						span: name.span,
						id: DefId::Port(name.id),
					});
				}
			}
			_ => ()
		}
	}
	None
}

fn search_hierarchy_items(items: &[ast::HierarchyItem], name: Name) -> Option<Def> {
	for item in items {
		let def = search_hierarchy_item(item, name);
		if def.is_some() {
			return def;
		}
	}
	None
}

fn search_hierarchy_item(item: &ast::HierarchyItem, name: Name) -> Option<Def> {
	match *item {
		ast::HierarchyItem::VarDecl(ref decl) => {
			// Also search through the type, as it may contain an enum whose
			// variant names we can bind against.
			if let Some(def) = search_type(&decl.ty, name) {
				return Some(def);
			}
			return search_var_decl_names(&decl.names, name);
		}
		ast::HierarchyItem::NetDecl(ref decl) => {
			// Also search through the type, as it may contain an enum whose
			// variant names we can bind against.
			if let Some(def) = search_type(&decl.ty, name) {
				return Some(def);
			}
			return search_var_decl_names(&decl.names, name);
		}
		ast::HierarchyItem::ParamDecl(ref pd) => match pd.kind {
			ast::ParamKind::Type(ref decls) => for decl in decls {
				if decl.name.name == name {
					return Some(Def {
						span: decl.name.span,
						id: DefId::Param(decl.name.id),
					});
				}
			},
			ast::ParamKind::Value(ref decls) => for decl in decls {
				if decl.name.name == name {
					return Some(Def {
						span: decl.name.span,
						id: DefId::Param(decl.name.id),
					});
				}
			},
		},
		ast::HierarchyItem::SubroutineDecl(ref decl) => {
			if decl.prototype.name.name == name {
				return Some(Def {
					span: decl.prototype.name.span,
					id: DefId::Subroutine(decl.prototype.name.id),
				});
			}
		}
		ast::HierarchyItem::PortDecl(ref decl) => for decl_name in &decl.names {
			if decl_name.name == name {
				return Some(Def {
					span: decl_name.name_span,
					id: DefId::Port(decl_name.id),
				});
			}
		},
		ast::HierarchyItem::Typedef(ref td) => {
			if td.name.name == name {
				return Some(Def {
					span: td.name.span,
					id: DefId::Typedef(td.name.id),
				});
			}
		}
		ast::HierarchyItem::ClassDecl(ref decl) => {
			if decl.name.name == name {
				return Some(Def {
					span: decl.name.span,
					id: DefId::Class(decl.name.id),
				});
			}
		}
		ast::HierarchyItem::Inst(ref insts) => for inst in &insts.names {
			if inst.name.name == name {
				return Some(Def {
					span: inst.name.span,
					id: DefId::Inst(inst.name.id),
				});
			}
		},
		_ => ()
	}
	None
}

fn search_var_decl_names(decls: &[ast::VarDeclName], name: Name) -> Option<Def> {
	for decl in decls {
		if decl.name == name {
			assert_renumbered!(decl.name_span, decl.id);
			return Some(Def {
				span: decl.name_span,
				id: DefId::Var(decl.id),
			});
		}
	}
	None
}

fn search_type(ty: &ast::Type, name: Name) -> Option<Def> {
	match ty.data {
		ast::EnumType(_, ref names) => {
			for n in names {
				if n.name.name == name {
					assert_renumbered!(n.name.span, n.name.id);
					return Some(Def {
						span: n.name.span,
						id: DefId::Var(n.name.id),
					});
				}
			}
			None
		}
		_ => None
	}
}

fn search_modport_decl(items: &[ast::HierarchyItem], name: Name) -> Option<Def> {
	for item in items {
		if let ast::HierarchyItem::ModportDecl(ref decl) = *item {
			for item in &decl.items {
				return Some(Def {
					span: item.name.span,
					id: DefId::Modport(item.name.id),
				})
			}
		}
	}
	None
}
