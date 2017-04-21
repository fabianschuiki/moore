// Copyright (c) 2017 Fabian Schuiki

//! This module implements AST node renumbering.

use super::ast::{self, NodeId};
use moore_common::errors::*;

pub fn renumber(asts: &mut [ast::Root]) {
	let mut rn = RenumberPass::new();
	for ast in asts {
		rn.renumber_ast(ast);
	}
}

struct RenumberPass {
	next_id: usize,
}

impl RenumberPass {
	pub fn new() -> RenumberPass {
		RenumberPass {
			next_id: 1,
		}
	}

	pub fn alloc_id(&mut self) -> NodeId {
		let n = NodeId::new(self.next_id);
		self.next_id += 1;
		n
	}

	pub fn renumber_ast(&mut self, ast: &mut ast::Root) {
		for item in &mut ast.items {
			self.renumber_item(item);
		}
	}

	pub fn renumber_item(&mut self, item: &mut ast::Item) {
		match *item {
			ast::Item::Module(ref mut decl) => {
				decl.id = self.alloc_id();
				self.renumber_param_ports(&mut decl.params);
				self.renumber_ports(&mut decl.ports);
				self.renumber_hierarchy_items(&mut decl.items);
			}
			ast::Item::Interface(ref mut decl) => {
				decl.id = self.alloc_id();
				self.renumber_ports(&mut decl.ports);
				self.renumber_hierarchy_items(&mut decl.items);
			}
			ast::Item::Package(ref mut decl) => {
				decl.id = self.alloc_id();
				self.renumber_hierarchy_items(&mut decl.items);
			}
			ast::Item::Item(ref mut item) => self.renumber_hierarchy_item(item),
		}
	}

	// TODO: Rename this function to renumber_param_decls.
	pub fn renumber_param_ports(&mut self, params: &mut [ast::ParamDecl]) {
		for param in params {
			self.renumber_param_port(param);
		}
	}

	// TODO: Replace this function with calls to renumber_param_decl.
	pub fn renumber_param_port(&mut self, param: &mut ast::ParamDecl) {
		self.renumber_param_decl(param);
		// param.name.id = self.alloc_id();
		// self.renumber_dims(&mut param.dims);
		// if let Some(ref mut e) = param.expr {
		// 	self.renumber_expr(e);
		// }
	}

	pub fn renumber_ports(&mut self, ports: &mut [ast::Port]) {
		for port in ports {
			self.renumber_port(port);
		}
	}

	pub fn renumber_port(&mut self, port: &mut ast::Port) {
		match *port {
			ast::Port::Intf { ref mut modport, ref mut name, ref mut dims, ref mut expr, .. } => {
				if let Some(ref mut modport) = *modport {
					modport.id = self.alloc_id();
				}
				name.id = self.alloc_id();
				self.renumber_dims(dims);
				if let Some(ref mut expr) = *expr {
					self.renumber_expr(expr);
				}
			}

			ast::Port::Explicit { ref mut name, ref mut expr, .. } => {
				name.id = self.alloc_id();
				if let Some(ref mut expr) = *expr {
					self.renumber_expr(expr);
				}
			}

			ast::Port::Named { ref mut ty, ref mut name, ref mut dims, ref mut expr, .. } => {
				self.renumber_type(ty);
				name.id = self.alloc_id();
				self.renumber_dims(dims);
				if let Some(ref mut expr) = *expr {
					self.renumber_expr(expr);
				}
			}

			ast::Port::Implicit(ref mut expr) => self.renumber_expr(expr),
		}
	}

	pub fn renumber_hierarchy_items(&mut self, items: &mut [ast::HierarchyItem]) {
		for item in items {
			self.renumber_hierarchy_item(item);
		}
	}

	pub fn renumber_hierarchy_item(&mut self, item: &mut ast::HierarchyItem) {
		match *item {
			ast::HierarchyItem::Procedure(ref mut prc) => self.renumber_stmt(&mut prc.stmt),
			ast::HierarchyItem::ImportDecl(ref mut decl) => self.renumber_import_decl(decl),
			ast::HierarchyItem::Assertion(ref mut assertion) => self.renumber_assertion(assertion),
			ast::HierarchyItem::VarDecl(ref mut decl) => self.renumber_var_decl(decl),
			ast::HierarchyItem::NetDecl(ref mut decl) => self.renumber_net_decl(decl),
			ast::HierarchyItem::ModportDecl(ref mut decl) => {
				for item in &mut decl.items {
					item.name.id = self.alloc_id();
					// TODO: Renumber modport_port_decls.
				}
			}
			ast::HierarchyItem::ParamDecl(ref mut decl) => self.renumber_param_decl(decl),
			ast::HierarchyItem::ContAssign(ref mut assign) => self.renumber_continuous_assignment(assign),
			ast::HierarchyItem::GenvarDecl(ref mut decls) => for decl in decls {
				decl.id = self.alloc_id();
				if let Some(ref mut e) = decl.init {
					self.renumber_expr(e);
				}
			},
			ast::HierarchyItem::GenerateRegion(_, ref mut items) => self.renumber_hierarchy_items(items),
			ast::HierarchyItem::GenerateFor(ref mut gf) => {
				self.renumber_stmt(&mut gf.init);
				self.renumber_expr(&mut gf.cond);
				self.renumber_expr(&mut gf.step);
				self.renumber_generate_block(&mut gf.block);
			}
			ast::HierarchyItem::GenerateIf(ref mut gi) => {
				self.renumber_expr(&mut gi.cond);
				self.renumber_generate_block(&mut gi.main_block);
				if let Some(ref mut b) = gi.else_block {
					self.renumber_generate_block(b);
				}
			}
			ast::HierarchyItem::GenerateCase(ref mut gc) => (),
			ast::HierarchyItem::Typedef(ref mut td) => self.renumber_typedef(td),
			ast::HierarchyItem::ClassDecl(ref mut decl) => self.renumber_class_decl(decl),

			// Unimplemented cases.
			ast::HierarchyItem::Dummy |
			ast::HierarchyItem::LocalparamDecl(_) |
			ast::HierarchyItem::ParameterDecl(_) |
			ast::HierarchyItem::PortDecl(_) |
			ast::HierarchyItem::SubroutineDecl(_) |
			ast::HierarchyItem::Inst(_) => ()
		}
	}

	pub fn renumber_generate_block(&mut self, block: &mut ast::GenerateBlock) {
		self.renumber_hierarchy_items(&mut block.items);
	}

	pub fn renumber_stmts(&mut self, stmts: &mut [ast::Stmt]) {
		for stmt in stmts {
			self.renumber_stmt(stmt);
		}
	}

	pub fn renumber_stmt(&mut self, stmt: &mut ast::Stmt) {
		match stmt.data {
			ast::SequentialBlock(ref mut stmts) |
			ast::ParallelBlock(ref mut stmts, _) => self.renumber_stmts(stmts),
			ast::IfStmt{ref mut cond, ref mut main_stmt, ref mut else_stmt, ..} => {
				self.renumber_expr(cond);
				self.renumber_stmt(main_stmt);
				if let Some(ref mut e) = *else_stmt {
					self.renumber_stmt(e);
				}
			}
			ast::BlockingAssignStmt{ref mut lhs, ref mut rhs, ..} => {
				self.renumber_expr(lhs);
				self.renumber_expr(rhs);
			}
			ast::NonblockingAssignStmt{ref mut lhs, ref mut rhs, ref mut delay, ref mut event, ..} => {
				self.renumber_expr(lhs);
				self.renumber_expr(rhs);
				if let Some(ref mut dc) = *delay {
					self.renumber_expr(&mut dc.expr);
				}
				if let Some(ref mut ec) = *event {
					unimplemented!();
					// self.renumber_event_control(ec);
				}
			}
			ast::TimedStmt(ref mut tc, ref mut stmt) => {
				self.renumber_timing_control(tc);
				self.renumber_stmt(stmt);
			}
			ast::CaseStmt{ref mut expr, ref mut items, ..} => {
				self.renumber_expr(expr);
				for item in items {
					match *item {
						ast::CaseItem::Default(ref mut stmt) => self.renumber_stmt(stmt),
						ast::CaseItem::Expr(ref mut exprs, ref mut stmt) => {
							for expr in exprs {
								self.renumber_expr(expr);
							}
							self.renumber_stmt(stmt);
						}
					}
				}
			}
			ast::ForeverStmt(ref mut stmt) => self.renumber_stmt(stmt),
			ast::RepeatStmt(ref mut expr, ref mut stmt) |
			ast::WhileStmt(ref mut expr, ref mut stmt) |
			ast::WaitExprStmt(ref mut expr, ref mut stmt) => {
				self.renumber_expr(expr);
				self.renumber_stmt(stmt);
			}
			ast::DoStmt(ref mut stmt, ref mut expr) => {
				self.renumber_stmt(stmt);
				self.renumber_expr(expr);
			}
			ast::ForStmt(ref mut init, ref mut cond, ref mut step, ref mut stmt) => {
				self.renumber_stmt(init);
				self.renumber_expr(cond);
				self.renumber_expr(step);
				self.renumber_stmt(stmt);
			}
			ast::ForeachStmt(ref mut expr, ref mut vars, ref mut stmt) => {
				self.renumber_expr(expr);
				for var in vars {
					if let Some(ref mut ident) = *var {
						ident.id = self.alloc_id();
					}
				}
			}
			ast::ExprStmt(ref mut expr) => self.renumber_expr(expr),
			ast::VarDeclStmt(ref mut decl) => self.renumber_var_decl(decl),
			ast::GenvarDeclStmt(ref mut decls) => for decl in decls { self.renumber_genvar_decl(decl); },
			ast::ReturnStmt(ref mut expr) => if let Some(ref mut e) = *expr { self.renumber_expr(e); },
			ast::ImportStmt(ref mut decl) => self.renumber_import_decl(decl),
			ast::AssertionStmt(ref mut assertion) => self.renumber_assertion(assertion),
			ast::DisableStmt(ref mut ident) => panic!("DisableStmt should contain an Ident that can be renumbered"),

			// Trivial cases.
			ast::NullStmt |
			ast::ContinueStmt |
			ast::BreakStmt |
			ast::WaitForkStmt |
			ast::DisableForkStmt => ()
		}
	}

	pub fn renumber_expr(&mut self, expr: &mut ast::Expr) {
		match expr.data {
			ast::IdentExpr(ref mut ident) |
			ast::SysIdentExpr(ref mut ident) => ident.id = self.alloc_id(),
			ast::IndexExpr{ref mut indexee, ref mut index} => {
				self.renumber_expr(indexee);
				self.renumber_expr(index);
			}
			ast::UnaryExpr{ref mut expr, ..} => self.renumber_expr(expr),
			ast::AssignExpr{ref mut lhs, ref mut rhs, ..} |
			ast::RangeExpr{ref mut lhs, ref mut rhs, ..} |
			ast::BinaryExpr{ref mut lhs, ref mut rhs, ..} => {
				self.renumber_expr(lhs);
				self.renumber_expr(rhs);
			},
			ast::TernaryExpr{ref mut cond, ref mut true_expr, ref mut false_expr, ..} => {
				self.renumber_expr(cond);
				self.renumber_expr(true_expr);
				self.renumber_expr(false_expr);
			},
			ast::CallExpr(ref mut expr, ref mut args) => {
				self.renumber_expr(expr);
				self.renumber_call_args(args);
			}
			ast::ConstructorCallExpr(ref mut args) => self.renumber_call_args(args),
			ast::ClassNewExpr(ref mut expr) => if let Some(ref mut e) = *expr { self.renumber_expr(e) },
			ast::ArrayNewExpr(ref mut expr, ref mut other) => {
				self.renumber_expr(expr);
				if let Some(ref mut e) = *other {
					self.renumber_expr(e);
				}
			}
			ast::StreamConcatExpr{ref mut slice, ref mut exprs} => {
				match *slice {
					Some(ast::StreamConcatSlice::Expr(ref mut expr)) => self.renumber_expr(expr),
					Some(ast::StreamConcatSlice::Type(ref mut ty)) => self.renumber_type(ty),
					None => (),
				}
				for expr in exprs {
					self.renumber_expr(&mut expr.expr);
					if let Some(ref mut e) = expr.range {
						self.renumber_expr(e);
					}
				}
			}
			ast::ConcatExpr{ref mut repeat, ref mut exprs} => {
				if let Some(ref mut r) = *repeat {
					self.renumber_expr(r);
				}
				for expr in exprs {
					self.renumber_expr(expr);
				}
			}
			ast::MinTypMaxExpr{ref mut min, ref mut typ, ref mut max} => {
				self.renumber_expr(min);
				self.renumber_expr(typ);
				self.renumber_expr(max);
			}
			ast::MemberExpr{ref mut expr, ref mut name} => {
				self.renumber_expr(expr);
				name.id = self.alloc_id();
			}
			ast::PatternExpr(ref mut fields) => for field in fields {
				match field.data {
					ast::PatternFieldData::Expr(ref mut expr) |
					ast::PatternFieldData::Default(ref mut expr) => self.renumber_expr(expr),
					ast::PatternFieldData::Member(ref mut a, ref mut b) => {
						self.renumber_expr(a);
						self.renumber_expr(b);
					}
					ast::PatternFieldData::Type(ref mut ty, ref mut expr) => {
						self.renumber_type(ty);
						self.renumber_expr(expr);
					}
					ast::PatternFieldData::Repeat(ref mut expr, ref mut exprs) => {
						self.renumber_expr(expr);
						for expr in exprs {
							self.renumber_expr(expr);
						}
					}
				}
			},

			// Trivial cases.
			ast::LiteralExpr(_) |
			ast::EmptyQueueExpr |
			ast::TypeExpr(_) => (),
			ast::DummyExpr => println!("{}", DiagBuilder2::warning("found dummy expression during renumbering").span(expr.span).add_note("you might want to fix the parser to produce an actual expression")),
		}
	}

	pub fn renumber_call_args(&mut self, args: &mut [ast::CallArg]) {
		for arg in args {
			self.renumber_call_arg(arg);
		}
	}

	pub fn renumber_call_arg(&mut self, arg: &mut ast::CallArg) {
		if let Some(ref mut e) = arg.expr {
			self.renumber_expr(e);
		}
	}

	pub fn renumber_timing_control(&mut self, tc: &mut ast::TimingControl) {
		match *tc {
			ast::TimingControl::Delay(ref mut dc) => self.renumber_expr(&mut dc.expr),
			ast::TimingControl::Event(ref mut ec) => self.renumber_event_control(ec),
			ast::TimingControl::Cycle(ref mut cd) => self.renumber_cycle_delay(cd),
		}
	}

	pub fn renumber_event_control(&mut self, ec: &mut ast::EventControl) {
		match ec.data {
			ast::EventControlData::Implicit => (),
			ast::EventControlData::Expr(ref mut expr) => self.renumber_event_expr(expr),
		}
	}

	pub fn renumber_cycle_delay(&mut self, cd: &mut ast::CycleDelay) {
		// TODO: Renumber cycle delay.
	}

	pub fn renumber_import_decl(&mut self, decl: &mut ast::ImportDecl) {
		for item in &mut decl.items {
			item.pkg.id = self.alloc_id();
			if let Some(ref mut ident) = item.name {
				ident.id = self.alloc_id();
			}
		}
	}

	pub fn renumber_assertion(&mut self, assertion: &mut ast::Assertion) {
		// TODO: Do something with the assertion label.
		match assertion.data {
			ast::AssertionData::Immediate(ref mut blk) |
			ast::AssertionData::Deferred(ref mut blk) => self.renumber_blocking_assertion(blk),
			ast::AssertionData::Concurrent(ref mut conc) => self.renumber_concurrent_assertion(conc),
		}
	}

	pub fn renumber_blocking_assertion(&mut self, assertion: &mut ast::BlockingAssertion) {
		match *assertion {
			ast::BlockingAssertion::Assert(ref mut expr, ref mut action) |
			ast::BlockingAssertion::Assume(ref mut expr, ref mut action) => {
				self.renumber_expr(expr);
				self.renumber_assertion_action_block(action);
			},
			ast::BlockingAssertion::Cover(ref mut expr, ref mut stmt) => {
				self.renumber_expr(expr);
				self.renumber_stmt(stmt);
			}
		}
	}

	pub fn renumber_concurrent_assertion(&mut self, assertion: &mut ast::ConcurrentAssertion) {
		match *assertion {
			ast::ConcurrentAssertion::AssertProperty(ref mut ps, ref mut action) |
			ast::ConcurrentAssertion::AssumeProperty(ref mut ps, ref mut action) |
			ast::ConcurrentAssertion::ExpectProperty(ref mut ps, ref mut action) => {
				self.renumber_propspec(ps);
				self.renumber_assertion_action_block(action);
			}
			ast::ConcurrentAssertion::CoverProperty(ref mut ps, ref mut stmt) => {
				self.renumber_propspec(ps);
				self.renumber_stmt(stmt);
			}
			ast::ConcurrentAssertion::CoverSequence => (),
			ast::ConcurrentAssertion::RestrictProperty(ref mut ps) => self.renumber_propspec(ps),
		}
	}

	pub fn renumber_propspec(&mut self, ps: &mut ast::PropSpec) {
		// TODO: Implement as soon as we have some property specs set up.
	}

	pub fn renumber_assertion_action_block(&mut self, action: &mut ast::AssertionActionBlock) {
		match *action {
			ast::AssertionActionBlock::Positive(ref mut stmt) |
			ast::AssertionActionBlock::Negative(ref mut stmt) => self.renumber_stmt(stmt),
			ast::AssertionActionBlock::Both(ref mut a, ref mut b) => {
				self.renumber_stmt(a);
				self.renumber_stmt(b);
			}
		}
	}

	pub fn renumber_event_expr(&mut self, expr: &mut ast::EventExpr) {
		match *expr {
			ast::EventExpr::Edge{ref mut value, ..} => self.renumber_expr(value),
			ast::EventExpr::Iff{ref mut expr, ref mut cond, ..} => {
				self.renumber_event_expr(expr);
				self.renumber_expr(cond);
			}
			ast::EventExpr::Or{ref mut lhs, ref mut rhs, ..} => {
				self.renumber_event_expr(lhs);
				self.renumber_event_expr(rhs);
			}
		}
	}

	pub fn renumber_var_decl(&mut self, decl: &mut ast::VarDecl) {
		self.renumber_type(&mut decl.ty);
		self.renumber_var_decl_names(&mut decl.names);
	}

	pub fn renumber_var_decl_names(&mut self, decls: &mut [ast::VarDeclName]) {
		for decl in decls {
			decl.id = self.alloc_id();
			self.renumber_dims(&mut decl.dims);
			if let Some(ref mut e) = decl.init {
				self.renumber_expr(e);
			}
		}
	}

	pub fn renumber_genvar_decl(&mut self, decl: &mut ast::GenvarDecl) {
		decl.id = self.alloc_id();
		if let Some(ref mut e) = decl.init {
			self.renumber_expr(e);
		}
	}

	pub fn renumber_dims(&mut self, dims: &mut [ast::TypeDim]) {
		for dim in dims {
			self.renumber_dim(dim);
		}
	}

	pub fn renumber_dim(&mut self, dim: &mut ast::TypeDim) {
		// TODO: Implement once type dim contains expressions.
	}

	pub fn renumber_type(&mut self, ty: &mut ast::Type) {
		match ty.data {
			ast::NamedType(ref mut name) => name.id = self.alloc_id(),
			ast::ScopedType{ty: ref mut super_ty, ref mut name, ..} => {
				self.renumber_type(super_ty);
				name.id = self.alloc_id();
			}

			ast::EnumType(ref mut inner, ref mut names) => {
				if let Some(ref mut i) = *inner {
					self.renumber_type(i);
				}
				for name in names {
					name.name.id = self.alloc_id();
					if let Some(ref mut e) = name.range {
						self.renumber_expr(e);
					}
					if let Some(ref mut e) = name.value {
						self.renumber_expr(e);
					}
				}
			}

			ast::StructType{ref mut members, ..} => for member in members {
				self.renumber_type(&mut member.ty);
				for name in &mut member.names {
					self.renumber_dims(&mut name.dims);
					if let Some(ref mut i) = name.init {
						self.renumber_expr(i);
					}
				}
			},

			ast::SpecializedType(ref mut ty, ref mut params) => {
				self.renumber_type(ty);
				// TODO: Renumber parameter assignments.
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
	}

	pub fn renumber_net_decl(&mut self, decl: &mut ast::NetDecl) {
		self.renumber_type(&mut decl.ty);
		if let Some(ref mut d) = decl.delay {
			self.renumber_expr(d);
		}
		self.renumber_var_decl_names(&mut decl.names);
	}

	pub fn renumber_continuous_assignment(&mut self, assign: &mut ast::ContAssign) {
		if let Some(ref mut e) = assign.delay {
			self.renumber_expr(e);
		}
		for &mut (ref mut lhs, ref mut rhs) in &mut assign.assignments {
			self.renumber_expr(lhs);
			self.renumber_expr(rhs);
		}
	}

	pub fn renumber_param_decl(&mut self, param: &mut ast::ParamDecl) {
		match param.kind {
			ast::ParamKind::Type(ref mut decls) => for decl in decls {
				decl.name.id = self.alloc_id();
				if let Some(ref mut ty) = decl.ty {
					self.renumber_type(ty);
				}
			},
			ast::ParamKind::Value(ref mut decls) => for decl in decls {
				self.renumber_type(&mut decl.ty);
				decl.name.id = self.alloc_id();
				self.renumber_dims(&mut decl.dims);
				if let Some(ref mut expr) = decl.expr {
					self.renumber_expr(expr);
				}
			},
		}
	}

	pub fn renumber_typedef(&mut self, td: &mut ast::Typedef) {
		td.name.id = self.alloc_id();
		self.renumber_type(&mut td.ty);
		self.renumber_dims(&mut td.dims);
	}

	pub fn renumber_class_decl(&mut self, decl: &mut ast::ClassDecl) {
		decl.name.id = self.alloc_id();
		self.renumber_param_ports(&mut decl.params);
		if let Some((ref mut ty, ref mut args)) = decl.extends {
			self.renumber_type(ty);
			self.renumber_call_args(args);
		}
		self.renumber_class_items(&mut decl.items)
	}

	pub fn renumber_class_items(&mut self, items: &mut [ast::ClassItem]) {
		for item in items {
			self.renumber_class_item(item);
		}
	}

	pub fn renumber_class_item(&mut self, item: &mut ast::ClassItem) {
		match item.data {
			ast::ClassItemData::Null => (),

			// Not yet implemented. This will show itself later when we try to
			// bind any of these.
			ast::ClassItemData::SubroutineDecl(_) |
			ast::ClassItemData::ExternSubroutine(_) |
			ast::ClassItemData::Constraint(_) |
			ast::ClassItemData::Property |
			ast::ClassItemData::ClassDecl |
			ast::ClassItemData::CovergroupDecl |
			ast::ClassItemData::LocalparamDecl(_) |
			ast::ClassItemData::ParameterDecl(_) => (),
		}
	}
}
