// Copyright (c) 2017 Fabian Schuiki

//! This module implements the scoreboard that drives the compilation of VHDL.

// #![allow(dead_code)]
#![allow(unused_imports)]

use std;
use std::fmt::Debug;
use std::collections::HashMap;
use std::cell::{RefCell, Cell};
use moore_common::Session;
use moore_common::name::*;
use moore_common::source::*;
use moore_common::errors::*;
use moore_common::NodeId;
use moore_common::score::{GenericContext, NodeStorage, NodeMaker, Result};
use syntax::ast;
use syntax::ast::{HasSpan, HasDesc};
use hir;
use typed_arena::Arena;
use llhd;
use ty::*;


/// The VHDL context which holds information about the language scoreboard and
/// the global scoreboard in its language-agnostic generic form. All useful
/// operations are defined on this context rather than on the scoreboard
/// directly, to decouple processing and ownership.
pub struct ScoreContext<'sb, 'ast: 'sb, 'ctx: 'sb> {
	/// The compiler session which carries the options and is used to emit
	/// diagnostics.
	pub sess: &'sb Session,
	/// The global context.
	pub global: &'sb GenericContext,
	/// The VHDL scoreboard.
	pub sb: &'sb ScoreBoard<'ast, 'ctx>,
}


/// The VHDL scoreboard that keeps track of compilation results.
pub struct ScoreBoard<'ast, 'ctx> {
	/// A reference to the arenas where the scoreboard allocates nodes.
	arenas: &'ctx Arenas,
	/// A table of library nodes. This is a filtered version of what the global
	/// scoreboard has, with only the VHDL nodes remaining.
	libs: RefCell<HashMap<LibRef, Vec<&'ast ast::DesignUnit>>>,
	/// A lookup table of library names.
	lib_names: RefCell<HashMap<Name, LibRef>>,
	/// A table of AST nodes.
	ast_table: RefCell<AstTable<'ast>>,
	/// A table of HIR nodes.
	hir_table: RefCell<HirTable<'ctx>>,
	/// A table of definitions in each scope.
	def_table: RefCell<HashMap<ScopeRef, &'ctx Defs>>,
	/// A table of architecture per entity and library.
	arch_table: RefCell<HashMap<LibRef, &'ctx ArchTable>>,
	/// The LLHD module into which code is emitted.
	pub llmod: RefCell<llhd::Module>,
	/// A table of LLHD declarations (i.e. prototypes). These are useful for
	/// example when an entity needs so be instantiated, for which only the
	/// signature of the entity is required, but not its full definition with
	/// its interior.
	lldecl_table: RefCell<HashMap<NodeId, llhd::ValueRef>>,
	/// A table of LLHD definitions.
	lldef_table: RefCell<HashMap<NodeId, llhd::ValueRef>>,
	/// A table of types.
	ty_table: RefCell<HashMap<NodeId, &'ctx Ty<'ctx>>>,
	/// A table of scopes.
	scope_table: RefCell<HashMap<ScopeRef, &'ctx Scope>>,
}


lazy_static! {
	static ref STD_LIB_REF: LibRef = LibRef(NodeId::alloc());
	static ref STANDARD_PKG_REF: BuiltinPkgRef = BuiltinPkgRef(NodeId::alloc());
	static ref TEXTIO_PKG_REF: BuiltinPkgRef = BuiltinPkgRef(NodeId::alloc());
	static ref ENV_PKG_REF: BuiltinPkgRef = BuiltinPkgRef(NodeId::alloc());
}


impl<'ast, 'ctx> ScoreBoard<'ast, 'ctx> {
	/// Creates a new empty VHDL scoreboard.
	pub fn new(arenas: &'ctx Arenas) -> ScoreBoard<'ast, 'ctx> {
		let nt = get_name_table();
		let mut pkg_defs = HashMap::new();
		let mut lib_names = HashMap::new();
		let mut def_table = HashMap::new();

		// Declare the builtin libraries and packages.
		pkg_defs.insert(
			nt.intern("standard", false).into(),
			vec![Spanned::new(Def::BuiltinPkg(*STANDARD_PKG_REF), INVALID_SPAN)]
		);
		pkg_defs.insert(
			nt.intern("textio", false).into(),
			vec![Spanned::new(Def::BuiltinPkg(*TEXTIO_PKG_REF), INVALID_SPAN)]
		);
		pkg_defs.insert(
			nt.intern("env", false).into(),
			vec![Spanned::new(Def::BuiltinPkg(*ENV_PKG_REF), INVALID_SPAN)]
		);
		lib_names.insert(nt.intern("std", false), *STD_LIB_REF);
		def_table.insert((*STD_LIB_REF).into(), &*arenas.defs.alloc(pkg_defs));

		// Assemble the scoreboard.
		ScoreBoard {
			arenas: arenas,
			libs: RefCell::new(HashMap::new()),
			lib_names: RefCell::new(lib_names),
			ast_table: RefCell::new(AstTable::new()),
			hir_table: RefCell::new(HirTable::new()),
			def_table: RefCell::new(def_table),
			arch_table: RefCell::new(HashMap::new()),
			llmod: RefCell::new(llhd::Module::new()),
			lldecl_table: RefCell::new(HashMap::new()),
			lldef_table: RefCell::new(HashMap::new()),
			ty_table: RefCell::new(HashMap::new()),
			scope_table: RefCell::new(HashMap::new()),
		}
	}
}


impl<'sb, 'ast, 'ctx> ScoreContext<'sb, 'ast, 'ctx> {
	/// Add a library of AST nodes. This function is called by the global
	/// scoreboard to add VHDL-specific AST nodes.
	pub fn add_library(&self, name: Name, id: LibRef, lib: Vec<&'ast ast::DesignUnit>) {
		self.sb.libs.borrow_mut().insert(id, lib);
		self.sb.lib_names.borrow_mut().insert(name, id);
	}


	/// Obtain the AST node corresponding to a node reference. The AST node must
	/// have previously been added to the `ast_table`, otherwise this function
	/// panics.
	pub fn ast<I>(&self, id: I) -> <AstTable<'ast> as NodeStorage<I>>::Node where
		I: 'ast + Copy + Debug,
		AstTable<'ast>: NodeStorage<I>,
		<AstTable<'ast> as NodeStorage<I>>::Node: Copy + Debug {
		match self.sb.ast_table.borrow().get(&id) {
			Some(node) => node,
			None => panic!("AST for {:?} should exist", id),
		}
	}


	/// Store an AST node in the scoreboard.
	pub fn set_ast<I>(&self, id: I, ast: <AstTable<'ast> as NodeStorage<I>>::Node)
	where
		I: Copy + Debug,
		AstTable<'ast>: NodeStorage<I>
	{
		self.sb.ast_table.borrow_mut().set(id, ast);
	}


	pub fn hir<I>(&self, id: I) -> Result<<HirTable<'ctx> as NodeStorage<I>>::Node> where
		I: 'ctx + Copy + Debug,
		HirTable<'ctx>: NodeStorage<I>,
		ScoreContext<'sb, 'ast, 'ctx>: NodeMaker<I, <HirTable<'ctx> as NodeStorage<I>>::Node>,
		<HirTable<'ctx> as NodeStorage<I>>::Node: Copy + Debug {

		if let Some(node) = self.sb.hir_table.borrow().get(&id) {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make hir for {:?}", id); }
		let node = self.make(id)?;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] hir for {:?} is {:?}", id, node); }
		self.sb.hir_table.borrow_mut().set(id, node);
		Ok(node)
	}


	pub fn defs(&self, id: ScopeRef) -> Result<&'ctx Defs> {
		if let Some(&node) = self.sb.def_table.borrow().get(&id) {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make defs for {:?}", id); }
		let node = self.make(id)?;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] defs for {:?} is {:?}", id, node); }
		if self.sb.def_table.borrow_mut().insert(id, node).is_some() {
			panic!("node should not exist");
		}
		Ok(node)
	}


	pub fn archs(&self, id: LibRef) -> Result<&'ctx ArchTable> {
		if let Some(&node) = self.sb.arch_table.borrow().get(&id) {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make arch for {:?}", id); }
		let node = self.make(id)?;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] arch for {:?} is {:?}", id, node); }
		if self.sb.arch_table.borrow_mut().insert(id, node).is_some() {
			panic!("node should not exist");
		}
		Ok(node)
	}


	pub fn lldecl<I>(&self, id: I) -> Result<llhd::ValueRef>
	where
		I: 'ctx + Copy + Debug + Into<NodeId>,
		ScoreContext<'sb, 'ast, 'ctx>: NodeMaker<I, DeclValueRef>
	{
		if let Some(node) = self.sb.lldecl_table.borrow().get(&id.into()).cloned() {
			return Ok(node);
		}
		if let Some(node) = self.sb.lldef_table.borrow().get(&id.into()).cloned() {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make lldecl for {:?}", id); }
		let node = self.make(id)?.0;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] lldecl for {:?} is {:?}", id, node); }
		if self.sb.lldecl_table.borrow_mut().insert(id.into(), node.clone()).is_some() {
			panic!("node should not exist");
		}
		Ok(node)
	}


	pub fn lldef<I>(&self, id: I) -> Result<llhd::ValueRef>
	where
		I: 'ctx + Copy + Debug + Into<NodeId>,
		ScoreContext<'sb, 'ast, 'ctx>: NodeMaker<I, DefValueRef>
	{
		if let Some(node) = self.sb.lldef_table.borrow().get(&id.into()).cloned() {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make lldef for {:?}", id); }
		let node = self.make(id)?.0;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] lldef for {:?} is {:?}", id, node); }
		if self.sb.lldef_table.borrow_mut().insert(id.into(), node.clone()).is_some() {
			panic!("node should not exist");
		}
		Ok(node)
	}


	pub fn ty<I>(&self, id: I) -> Result<&'ctx Ty<'ctx>>
	where
		I: 'ctx + Copy + Debug + Into<NodeId>,
		ScoreContext<'sb, 'ast, 'ctx>: NodeMaker<I, &'ctx Ty<'ctx>>
	{
		if let Some(node) = self.sb.ty_table.borrow().get(&id.into()).cloned() {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make ty for {:?}", id); }
		let node = self.make(id)?;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] ty for {:?} is {:?}", id, node); }
		if self.sb.ty_table.borrow_mut().insert(id.into(), node).is_some() {
			panic!("node should not exist");
		}
		Ok(node)
	}


	pub fn scope(&self, id: ScopeRef) -> Result<&'ctx Scope> {
		if let Some(node) = self.sb.scope_table.borrow().get(&id.into()).cloned() {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make scope for {:?}", id); }
		let node = self.make(id)?;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] scope for {:?} is {:?}", id, node); }
		if self.sb.scope_table.borrow_mut().insert(id, node).is_some() {
			panic!("node should not exist");
		}
		Ok(node)
	}
}


// Wrapper types around ValueRef such that we can distinguish in the
// scoreboard's implementations of the NodeMaker trait whether we're building a
// declaration or definition.
#[derive(Debug, Clone)]
pub struct DeclValueRef(pub llhd::ValueRef);
#[derive(Debug, Clone)]
pub struct DefValueRef(pub llhd::ValueRef);


// Library lowering to HIR.
impl<'sb, 'ast, 'ctx> NodeMaker<LibRef, &'ctx hir::Lib> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: LibRef) -> Result<&'ctx hir::Lib> {
		let mut lib = hir::Lib::new();
		for du in &self.sb.libs.borrow()[&id] {
			let ctx_id = CtxItemsRef(NodeId::alloc());
			self.set_ast(ctx_id, (id.into(), du.ctx.as_slice()));
			match du.data {
				ast::DesignUnitData::EntityDecl(ref decl) => {
					let subid = EntityRef(NodeId::alloc());
					self.set_ast(subid, (id, ctx_id, decl));
					lib.entities.push(subid);
				}
				ast::DesignUnitData::CfgDecl(ref decl) => {
					let subid = CfgRef(NodeId::alloc());
					self.set_ast(subid, (id, ctx_id, decl));
					lib.cfgs.push(subid);
				}
				ast::DesignUnitData::PkgDecl(ref decl) => {
					let subid = PkgDeclRef(NodeId::alloc());
					self.set_ast(subid, (id, ctx_id, decl));
					lib.pkg_decls.push(subid);
				}
				ast::DesignUnitData::PkgInst(ref decl) => {
					let subid = PkgInstRef(NodeId::alloc());
					self.set_ast(subid, (id, ctx_id, decl));
					lib.pkg_insts.push(subid);
				}
				ast::DesignUnitData::CtxDecl(ref decl) => {
					let subid = CtxRef(NodeId::alloc());
					self.set_ast(subid, (id, ctx_id, decl));
					lib.ctxs.push(subid);
				}
				ast::DesignUnitData::ArchBody(ref decl) => {
					let subid = ArchRef(NodeId::alloc());
					self.set_ast(subid, (id, ctx_id, decl));
					lib.archs.push(subid);
				}
				ast::DesignUnitData::PkgBody(ref decl) => {
					let subid = PkgBodyRef(NodeId::alloc());
					self.set_ast(subid, (id, ctx_id, decl));
					lib.pkg_bodies.push(subid);
				}
			}
		}
		Ok(self.sb.arenas.hir.lib.alloc(lib))
	}
}


// Lower an entity to HIR.
impl<'sb, 'ast, 'ctx> NodeMaker<EntityRef, &'ctx hir::Entity> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: EntityRef) -> Result<&'ctx hir::Entity> {
		let (lib, ctx_id, ast) = self.ast(id);
		let mut entity = hir::Entity{
			parent: ctx_id.into(),
			lib: lib,
			name: ast.name,
			generics: Vec::new(),
			ports: Vec::new(),
		};
		let mut port_spans = Vec::new();
		let mut generic_spans = Vec::new();
		for decl in &ast.decls {
			match *decl {
				// Port clauses
				ast::DeclItem::PortgenClause(_, Spanned{ value: ast::PortgenKind::Port, span }, ref decls) => {
					// For ports only signal interface declarations are allowed.
					port_spans.push(span);
					for decl in &decls.value {
						match *decl {
							ast::IntfDecl::ObjDecl(ref decl @ ast::IntfObjDecl{ kind: ast::IntfObjKind::Signal, .. }) => {
								let ty = SubtypeIndRef(NodeId::alloc());
								self.set_ast(ty, (id.into(), &decl.ty));
								for name in &decl.names {
									let subid = IntfSignalRef(NodeId::alloc());
									self.set_ast(subid, (id.into(), decl, ty, name));
									entity.ports.push(subid);
								}
							}
							ref wrong => {
								self.sess.emit(
									DiagBuilder2::error(format!("A {} cannot appear in a port clause", wrong.desc()))
									.span(wrong.human_span())
								);
								continue;
							}
						}
					}
				}

				// Generic clauses
				ast::DeclItem::PortgenClause(_, Spanned{ value: ast::PortgenKind::Generic, span }, ref decls) => {
					// For generics only constant, type, subprogram, and package
					// interface declarations are allowed.
					generic_spans.push(span);
					for decl in &decls.value {
						match *decl {
							ast::IntfDecl::TypeDecl(ref decl) => {
								let subid = IntfTypeRef(NodeId::alloc());
								self.set_ast(subid, (id.into(), decl));
								entity.generics.push(subid.into());
							}
							ast::IntfDecl::SubprogSpec(ref decl) => {
								let subid = IntfSubprogRef(NodeId::alloc());
								self.set_ast(subid, (id.into(), decl));
								entity.generics.push(subid.into());
							}
							ast::IntfDecl::PkgInst(ref decl) => {
								let subid = IntfPkgRef(NodeId::alloc());
								self.set_ast(subid, (id.into(), decl));
								entity.generics.push(subid.into());
							}
							ast::IntfDecl::ObjDecl(ref decl @ ast::IntfObjDecl{ kind: ast::IntfObjKind::Const, .. }) => {
								let ty = SubtypeIndRef(NodeId::alloc());
								self.set_ast(ty, (id.into(), &decl.ty));
								for name in &decl.names {
									let subid = IntfConstRef(NodeId::alloc());
									self.set_ast(subid, (id.into(), decl, ty, name));
									entity.generics.push(subid.into());
								}
							}
							ref wrong => {
								self.sess.emit(
									DiagBuilder2::error(format!("A {} cannot appear in a generic clause", wrong.desc()))
									.span(wrong.human_span())
								);
								continue;
							}
						}
					}
				}

				ref wrong => {
					self.sess.emit(
						DiagBuilder2::error(format!("A {} cannot appear in an entity declaration", wrong.desc()))
						.span(decl.human_span())
					);
					continue;
				}
			}
		}
		// TODO(strict): Complain about multiple port and generic clauses.
		// TODO(strict): Complain when port and generic clauses are not the
		// first in the entity.
		Ok(self.sb.arenas.hir.entity.alloc(entity))
	}
}


// Lower an interface signal to HIR.
impl<'sb, 'ast, 'ctx> NodeMaker<IntfSignalRef, &'ctx hir::IntfSignal> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: IntfSignalRef) -> Result<&'ctx hir::IntfSignal> {
		let (_, decl, subty_id, ident) = self.ast(id);
		let init = match decl.default {
			Some(ref e) => {
				let subid = ExprRef(NodeId::alloc());
				self.set_ast(subid, (id.into(), e));
				Some(subid)
			}
			None => None
		};
		let sig = hir::IntfSignal {
			name: Spanned::new(ident.name, ident.span),
			mode: match decl.mode {
				None | Some(ast::IntfMode::In) => hir::IntfSignalMode::In,
				Some(ast::IntfMode::Out) => hir::IntfSignalMode::Out,
				Some(ast::IntfMode::Inout) => hir::IntfSignalMode::Inout,
				Some(ast::IntfMode::Buffer) => hir::IntfSignalMode::Buffer,
				Some(ast::IntfMode::Linkage) => hir::IntfSignalMode::Linkage,
			},
			ty: subty_id,
			bus: decl.bus,
			init: init,
		};
		Ok(self.sb.arenas.hir.intf_sig.alloc(sig))
	}
}


// Lower a subtype indication to HIR.
impl<'sb, 'ast, 'ctx> NodeMaker<SubtypeIndRef, &'ctx hir::SubtypeInd> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: SubtypeIndRef) -> Result<&'ctx hir::SubtypeInd> {
		let (scope_id, ast) = self.ast(id);

		// TODO: Implement resolution indications.
		if let Some(_) = ast.res {
			self.sess.emit(
				DiagBuilder2::error("Resolution indications on subtypes not yet supported")
				.span(ast.span)
			);
		}

		// Separate the type mark from the constraint.
		// let scope = self.scope(scope_id)?;
		let out = self.resolve_compound_name(&ast.name, scope_id)?;
		println!("primary resolved to {:?}", out);

		Ok(self.sb.arenas.hir.subtype_ind.alloc(hir::SubtypeInd{
			span: ast.span,
			type_mark: (),
		}))
	}
}

impl<'sb, 'ast, 'ctx> ScoreContext<'sb, 'ast, 'ctx> {
	/// Convert a primary name as it is present in the AST to a resolvable name
	/// that can be defined and resolved in a scope.
	pub fn resolvable_from_primary_name(&self, primary: &ast::PrimaryName) -> Result<Spanned<ResolvableName>> {
		match primary.kind {
			ast::PrimaryNameKind::Ident(n) => Ok(Spanned::new(ResolvableName::Ident(n), primary.span)),
			ast::PrimaryNameKind::Char(c) => Ok(Spanned::new(ResolvableName::Bit(c), primary.span)),
			ast::PrimaryNameKind::String(s) => {
				// Declare a static table that maps operator symbols to the
				// actual operator.
				lazy_static!(static ref TBL: HashMap<Name, Operator> = {
					let mut tbl = HashMap::new();
					let nt = get_name_table();
					tbl.insert(nt.intern("and",  false), Operator::Logical(ast::LogicalOp::And));
					tbl.insert(nt.intern("or",   false), Operator::Logical(ast::LogicalOp::Or));
					tbl.insert(nt.intern("nand", false), Operator::Logical(ast::LogicalOp::Nand));
					tbl.insert(nt.intern("nor",  false), Operator::Logical(ast::LogicalOp::Nor));
					tbl.insert(nt.intern("xor",  false), Operator::Logical(ast::LogicalOp::Xor));
					tbl.insert(nt.intern("xnor", false), Operator::Logical(ast::LogicalOp::Xnor));
					tbl.insert(nt.intern("=",    false), Operator::Rel(ast::RelationalOp::Eq));
					tbl.insert(nt.intern("/=",   false), Operator::Rel(ast::RelationalOp::Neq));
					tbl.insert(nt.intern("<",    false), Operator::Rel(ast::RelationalOp::Lt));
					tbl.insert(nt.intern("<=",   false), Operator::Rel(ast::RelationalOp::Leq));
					tbl.insert(nt.intern(">",    false), Operator::Rel(ast::RelationalOp::Gt));
					tbl.insert(nt.intern(">=",   false), Operator::Rel(ast::RelationalOp::Geq));
					tbl.insert(nt.intern("?=",   false), Operator::Match(ast::RelationalOp::Eq));
					tbl.insert(nt.intern("?/=",  false), Operator::Match(ast::RelationalOp::Neq));
					tbl.insert(nt.intern("?<",   false), Operator::Match(ast::RelationalOp::Lt));
					tbl.insert(nt.intern("?<=",  false), Operator::Match(ast::RelationalOp::Leq));
					tbl.insert(nt.intern("?>",   false), Operator::Match(ast::RelationalOp::Gt));
					tbl.insert(nt.intern("?>=",  false), Operator::Match(ast::RelationalOp::Geq));
					tbl.insert(nt.intern("sll",  false), Operator::Shift(ast::ShiftOp::Sll));
					tbl.insert(nt.intern("srl",  false), Operator::Shift(ast::ShiftOp::Srl));
					tbl.insert(nt.intern("sla",  false), Operator::Shift(ast::ShiftOp::Sla));
					tbl.insert(nt.intern("sra",  false), Operator::Shift(ast::ShiftOp::Sra));
					tbl.insert(nt.intern("rol",  false), Operator::Shift(ast::ShiftOp::Rol));
					tbl.insert(nt.intern("ror",  false), Operator::Shift(ast::ShiftOp::Ror));
					tbl.insert(nt.intern("+",    false), Operator::Add);
					tbl.insert(nt.intern("-",    false), Operator::Sub);
					tbl.insert(nt.intern("&",    false), Operator::Concat);
					tbl.insert(nt.intern("*",    false), Operator::Mul);
					tbl.insert(nt.intern("/",    false), Operator::Div);
					tbl.insert(nt.intern("mod",  false), Operator::Mod);
					tbl.insert(nt.intern("rem",  false), Operator::Rem);
					tbl.insert(nt.intern("**",   false), Operator::Pow);
					tbl.insert(nt.intern("abs",  false), Operator::Abs);
					tbl.insert(nt.intern("not",  false), Operator::Not);
					tbl
				};);

				// Try to find an operator for the provided name. If none is in
				// the above table, emit an error.
				match TBL.get(&s) {
					Some(&op) => Ok(Spanned::new(ResolvableName::Operator(op), primary.span)),
					None => {
						self.sess.emit(
							DiagBuilder2::error(format!("`{}` is not a valid operator symbol", s))
							.span(primary.span)
							.add_note("see IEEE 1076-2008 section 9.2 for a list of operators")
						);
						Err(())
					}
				}
			}
		}
	}


	/// Resolve a name within a scope. Traverses to the parent scopes if nothing
	/// matching the name is found.
	pub fn resolve_name(&self, name: Spanned<ResolvableName>, scope_id: ScopeRef) -> Result<Vec<Spanned<Def>>> {
		println!("[SB][VHDL] resolve {:?} in scope {:?}", name.value, scope_id);
		let scope = self.scope(scope_id)?;
		let mut found_defs = Vec::new();
		for &defs_id in &scope.defs {
			let defs = self.defs(defs_id)?;
			if let Some(d) = defs.get(&name.value) {
				found_defs.extend(d);
			}
		}

		// If nothing matched the definition, try to escalate to the parent
		// scope. If there is no parent scope, i.e. we're the parent, fail with
		// a diagnostic.
		if found_defs.is_empty() {
			if let Some(parent_id) = scope.parent {
				self.resolve_name(name, parent_id)
			} else {
				self.sess.emit(DiagBuilder2::error(format!("`{}` is not known", name.value)).span(name.span));
				Err(())
			}
		} else {
			println!("[SB][VHDL] resolved {:?} to {:?}", name.value, found_defs);
			Ok(found_defs)
		}
	}


	pub fn resolve_compound_name<'a>(&self, name: &'a ast::CompoundName, scope_id: ScopeRef) -> Result<(Vec<Spanned<Def>>, &'a [ast::NamePart])> {
		println!("[SB][VHDL] resolve compound {:?} in scope {:?}", name, scope_id);

		// First resolve the primary name.
		let mut last_span = name.primary.span;
		let mut defs = self.resolve_name(self.resolvable_from_primary_name(&name.primary)?, scope_id)?;

		// Resolve as many name parts as possible.
		for i in 0..name.parts.len() {
			match name.parts[i] {
				ast::NamePart::Select(ref pn) => {
					// Ensure that we only have one definition, i.e. that the
					// name up to this point is not ambiguous.
					let def = if defs.len() == 1 {
						defs[0]
					} else {
						let start = name.span.begin().into();
						let span = Span::union(start, last_span);
						let span_str = span.extract();
						let mut d = DiagBuilder2::error(format!("`{}` is ambiguous", span_str))
							.span(span)
							.add_note(format!("`{}` refers to the following {} items:", span_str, defs.len()));
						for def in &defs {
							d = d.span(def.span);
						}
						self.sess.emit(d);
						return Err(());
					};

					// Make sure that we can map the definition to a scope
					// reference. We can only select into things that have a
					// scope of their own.
					let scope = match def.value {
						Def::Lib(id) => id.into(),
						Def::BuiltinPkg(id) => id.into(),
						d => {
							self.sess.emit(
								DiagBuilder2::error(format!("Cannot select into {:?}", d))
								.span(pn.span)
							);
							return Err(());
						}
					};

					// Perform the name resolution in the scope determined
					// above.
					last_span = pn.span;
					defs = self.resolve_name(self.resolvable_from_primary_name(pn)?, scope)?;
				}

				// All other name parts we do not resolve and simply pass back
				// to the caller.
				_ => return Ok((defs, &name.parts[i..]))
			}
		}

		// If we arrive here, we were able to resolve the entire name. So we
		// simply return the definitions found and an empty slice of remaining
		// parts.
		Ok((defs, &[]))
	}
}


// Definitions in a scope.
impl<'sb, 'ast, 'ctx> NodeMaker<ScopeRef, &'ctx Defs> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: ScopeRef) -> Result<&'ctx Defs> {
		match id {
			ScopeRef::Lib(id) => self.make(id),
			ScopeRef::CtxItems(id) => self.make(id),
			ScopeRef::Entity(id) => self.make(id),
			ScopeRef::BuiltinPkg(id) => Ok(&(*BUILTIN_PKG_DEFS)[&id])
		}
	}
}


// Definitions in a library.
impl<'sb, 'ast, 'ctx> NodeMaker<LibRef, &'ctx Defs> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: LibRef) -> Result<&'ctx Defs> {
		// Approach:
		// 1) Get the HIR of the library
		// 2) Gather definitions from the HIR.
		// 3) Create defs and return.
		let lib = self.hir(id)?;

		// Assemble an uber-iterator that will iterate over each
		// definition in the library. We do this by obtaining an
		// iterator for every design unit type in the library, then
		// mapping each ID to the corresponding name and definition.
		// The name is determined by looking up the AST node of the
		// design unit to be defined.
		let iter = lib.entities.iter().map(|&n| (self.ast(n).2.name, Def::Entity(n)));
		let iter = iter.chain(lib.cfgs.iter().map(|&n| (self.ast(n).2.name, Def::Cfg(n))));
		let iter = iter.chain(lib.pkg_decls.iter().map(|&n| (self.ast(n).2.name, Def::Pkg(n))));
		let iter = iter.chain(lib.pkg_insts.iter().map(|&n| (self.ast(n).2.name, Def::PkgInst(n))));
		let iter = iter.chain(lib.ctxs.iter().map(|&n| (self.ast(n).2.name, Def::Ctx(n))));

		// For every element the iterator produces, add it to the map of
		// definitions.
		let mut defs = HashMap::new();
		for (name, def) in iter {
			defs.entry(name.value.into()).or_insert_with(|| Vec::new()).push(Spanned::new(def, name.span));
		}

		// Warn the user about duplicate definitions.
		let mut had_dups = false;
		for (name, defs) in &defs {
			if defs.len() <= 1 {
				continue;
			}
			let mut d = DiagBuilder2::error(format!("`{}` declared multiple times", name));
			for def in defs {
				d = d.span(def.span);
			}
			self.sess.emit(d);
			had_dups = true;
		}
		if had_dups {
			return Err(());
		}

		// Return the definitions.
		Ok(self.sb.arenas.defs.alloc(defs))
	}
}


// Definitions made by the context items that appear before design units.
impl<'sb, 'ast, 'ctx> NodeMaker<CtxItemsRef, &'ctx Defs> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: CtxItemsRef) -> Result<&'ctx Defs> {
		let (_, ast) = self.ast(id);
		let mut defs = HashMap::new();
		let mut has_fails = false;
		for item in ast {
			// For each name in a library clause, find the corresponding library
			// and create a definition for it.
			match *item {
				ast::CtxItem::LibClause(Spanned{ value: ref names, .. }) => {
					for ident in names {
						if let Some(&lib_id) = self.sb.lib_names.borrow().get(&ident.name) {
							let mut defs = defs.entry(ident.name.into()).or_insert_with(||vec![]);
							if !defs.is_empty() {
								self.sess.emit(
									DiagBuilder2::error(format!("`{}` has already been declared", ident.name))
									.span(ident.span)
									// TODO: Show previous declarations
								);
								has_fails = true;
							} else {
								defs.push(Spanned::new(Def::Lib(lib_id), ident.span));
							}
						} else {
							self.sess.emit(
								DiagBuilder2::error(format!("no library named `{}` found", ident.name))
								.span(ident.span)
								// TODO: Print list of libraries.
							);
							has_fails = true;
						}
					}
				}
				_ => ()
			}
		}
		if has_fails {
			Err(())
		} else {
			Ok(self.sb.arenas.defs.alloc(defs))
		}
	}
}


// Definitions in an entity.
impl<'sb, 'ast, 'ctx> NodeMaker<EntityRef, &'ctx Defs> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, _: EntityRef) -> Result<&'ctx Defs> {
		// TODO: Implement this.
		Ok(self.sb.arenas.defs.alloc(HashMap::new()))
	}
}


// Group the architectures declared in a library by entity.
impl<'sb, 'ast, 'ctx> NodeMaker<LibRef, &'ctx ArchTable> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: LibRef) -> Result<&'ctx ArchTable> {
		let lib = self.hir(id)?;
		let defs = self.defs(ScopeRef::Lib(id.into()))?;
		let mut res = ArchTable::new();
		res.by_entity = lib.entities.iter().map(|&id| (id, EntityArchTable::new())).collect();
		let mut had_fails = false;
		for &arch_ref in &lib.archs {
			let arch = self.ast(arch_ref).2;

			// Extract a simple entity name for now. Maybe we need to support
			// the full-blown compound names at some point?
			let entity_name = match if arch.target.parts.is_empty() {
				match arch.target.primary.kind {
					ast::PrimaryNameKind::Ident(n) => Some(n),
					_ => None,
				}
			} else {
				None
			}{
				Some(n) => n,
				None => {
					self.sess.emit(
						DiagBuilder2::error(format!("`{}` is not a valid entity name", arch.target.span.extract()))
						.span(arch.target.span)
					);
					had_fails = true;
					continue;
				}
			};

			// Try to find the entity with the name.
			let entity = match defs.get(&entity_name.into()) {
				Some(e) => {
					let last = e.last().unwrap();
					match last.value {
						Def::Entity(e) => e,
						_ => {
							self.sess.emit(
								DiagBuilder2::error(format!("`{}` is not an entity", entity_name))
								.span(arch.target.span)
								.add_note(format!("`{}` defined here:", entity_name))
								.span(last.span)
							);
							had_fails = true;
							continue;
						}
					}
				}
				None => {
					self.sess.emit(
						DiagBuilder2::error(format!("Unknown entity `{}`", entity_name))
						.span(arch.target.span)
					);
					had_fails = true;
					continue;
				}
			};

			// Insert the results into the table of architectures for the found
			// entity.
			let entry = res.by_entity.get_mut(&entity).unwrap();
			entry.ordered.push(arch_ref);
			entry.by_name.insert(arch.name.value, arch_ref);
			res.by_arch.insert(arch_ref, entity);
		}
		if had_fails {
			Err(())
		} else {
			Ok(self.sb.arenas.archs.alloc(res))
		}
	}
}


// Generate the prototype for an architecture.
impl<'sb, 'ast, 'ctx> NodeMaker<ArchRef, DeclValueRef> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: ArchRef) -> Result<DeclValueRef> {
		unimplemented!("llhd decl for {:?}", id);
	}
}


// Generate the definition for an architecture.
impl<'sb, 'ast, 'ctx> NodeMaker<ArchRef, DefValueRef> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: ArchRef) -> Result<DefValueRef> {
		let arch = self.ast(id);
		let entity_id = *self.archs(arch.0)?.by_arch.get(&id).unwrap();
		let entity = self.hir(entity_id)?;

		// Assemble the types and names for the entity.
		println!("entity ports: {:?}", entity.ports);
		let mut in_tys    = Vec::new();
		let mut out_tys   = Vec::new();
		let mut in_names  = Vec::new();
		let mut out_names = Vec::new();
		for &port in &entity.ports {
			let hir = self.hir(port)?;
			self.ty(hir.ty)?; // for now just ask for the type directly
			let ty = llhd::void_ty();
			match hir.mode {
				hir::IntfSignalMode::In | hir::IntfSignalMode::Inout | hir::IntfSignalMode::Linkage => {
					in_tys.push(ty.clone());
					in_names.push(hir.name.value);
				}
				_ => ()
			}
			match hir.mode {
				hir::IntfSignalMode::Out | hir::IntfSignalMode::Inout | hir::IntfSignalMode::Buffer => {
					out_tys.push(ty.clone());
					out_names.push(hir.name.value);
				}
				_ => ()
			}
		}

		// TODO: Actually get the lltype of the entity for this.
		let ty = llhd::entity_ty(in_tys, out_tys);

		// Create a new entity into which we will generate all the code.
		let name = format!("{}_{}", entity.name.value, arch.2.name.value);
		let mut entity = llhd::Entity::new(name, ty);

		// Assign names to the arguments. This is merely cosmetic, but makes the
		// emitted LLHD easier to read.
		for (arg, &name) in entity.inputs_mut().iter_mut().zip(in_names.iter()) {
			arg.set_name(name.as_str().to_owned());
		}
		for (arg, &name) in entity.outputs_mut().iter_mut().zip(out_names.iter()) {
			arg.set_name(name.as_str().to_owned());
		}

		// Add the entity to the module and return a reference to it.
		Ok(DefValueRef(self.sb.llmod.borrow_mut().add_entity(entity).into()))
	}
}


// Determine the type represented by a subtype indication.
impl<'sb, 'ast, 'ctx> NodeMaker<SubtypeIndRef, &'ctx Ty<'ctx>> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: SubtypeIndRef) -> Result<&'ctx Ty<'ctx>> {
		let hir = self.hir(id)?;
		println!("hir of subtype is {:?}", hir);
		self.sess.emit(DiagBuilder2::error("Type calculation not implemented").span(hir.span));
		Err(())
	}
}


// Populate a scope.
impl<'sb, 'ast, 'ctx> NodeMaker<ScopeRef, &'ctx Scope> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: ScopeRef) -> Result<&'ctx Scope> {
		match id {
			ScopeRef::Lib(id) => self.make(id),
			ScopeRef::CtxItems(id) => self.make(id),
			ScopeRef::Entity(id) => self.make(id),
			ScopeRef::BuiltinPkg(id) => Ok(&(*BUILTIN_PKG_SCOPES)[&id])
		}
	}
}


// Populate the scope of an library.
impl<'sb, 'ast, 'ctx> NodeMaker<LibRef, &'ctx Scope> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: LibRef) -> Result<&'ctx Scope> {
		let mut defs = Vec::new();
		defs.push(id.into());
		Ok(self.sb.arenas.scope.alloc(Scope{
			parent: None,
			defs: defs,
		}))
	}
}


// Populate the scope of the context items that appear before a design unit. The
// scope of the design unit itself is a subscope of the context items.
impl<'sb, 'ast, 'ctx> NodeMaker<CtxItemsRef, &'ctx Scope> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: CtxItemsRef) -> Result<&'ctx Scope> {
		let mut defs = Vec::new();
		defs.push(id.into());
		// TODO: Resolve use clauses.
		Ok(self.sb.arenas.scope.alloc(Scope{
			parent: None,
			defs: defs,
		}))
	}
}


// Populate the scope of an entity.
impl<'sb, 'ast, 'ctx> NodeMaker<EntityRef, &'ctx Scope> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: EntityRef) -> Result<&'ctx Scope> {
		let hir = self.hir(id)?;
		let mut defs = Vec::new();
		defs.push(id.into());
		// TODO: Resolve use clauses and add whatever they bring into scope to
		// the defs array.
		Ok(self.sb.arenas.scope.alloc(Scope{
			parent: Some(hir.parent),
			defs: defs,
		}))
	}
}


/// A collection of arenas that the scoreboard uses to allocate its nodes.
pub struct Arenas {
	pub hir: hir::Arenas,
	pub defs: Arena<Defs>,
	pub archs: Arena<ArchTable>,
	pub scope: Arena<Scope>,
}


impl Arenas {
	/// Create a new set of arenas.
	pub fn new() -> Arenas {
		Arenas {
			hir: hir::Arenas::new(),
			defs: Arena::new(),
			archs: Arena::new(),
			scope: Arena::new(),
		}
	}
}


/// A table of the architectures in a library, and how they relate to the
/// entities.
#[derive(Debug)]
pub struct ArchTable {
	pub by_arch: HashMap<ArchRef, EntityRef>,
	pub by_entity: HashMap<EntityRef, EntityArchTable>,
}

/// A table of the architectures associated with an entity.
#[derive(Debug)]
pub struct EntityArchTable {
	pub ordered: Vec<ArchRef>,
	pub by_name: HashMap<Name, ArchRef>,
}

impl ArchTable {
	pub fn new() -> ArchTable {
		ArchTable {
			by_arch: HashMap::new(),
			by_entity: HashMap::new(),
		}
	}
}

impl EntityArchTable {
	pub fn new() -> EntityArchTable {
		EntityArchTable {
			ordered: Vec::new(),
			by_name: HashMap::new(),
		}
	}
}


/// A set of names and definitions.
pub type Defs = HashMap<ResolvableName, Vec<Spanned<Def>>>;


/// A scope.
#[derive(Debug)]
pub struct Scope {
	/// The parent scope to which name resolution progresses if this scoped does
	/// not provide the required definition.
	pub parent: Option<ScopeRef>,
	/// The definitions visible within this scope. Note that these are
	/// references to Defs in the scoreboard, not the definitions themselves.
	pub defs: Vec<ScopeRef>,
}


/// A name that can be resolved in a scope.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ResolvableName {
	Ident(Name),
	Bit(char),
	Operator(Operator),
}

impl std::fmt::Display for ResolvableName {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			ResolvableName::Ident(n)    => write!(f, "{}", n),
			ResolvableName::Bit(n)      => write!(f, "{}", n),
			ResolvableName::Operator(n) => write!(f, "{}", n),
		}
	}
}

impl From<Name> for ResolvableName {
	fn from(name: Name) -> ResolvableName {
		ResolvableName::Ident(name)
	}
}


/// An operator as defined in IEEE 1076-2008 section 9.2.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operator {
	Logical(ast::LogicalOp),
	Rel(ast::RelationalOp),
	Match(ast::RelationalOp),
	Shift(ast::ShiftOp),
	Add,
	Sub,
	Concat,
	Mul,
	Div,
	Mod,
	Rem,
	Pow,
	Abs,
	Not
}

impl std::fmt::Display for Operator {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			Operator::Logical(ast::LogicalOp::And)  => write!(f, "and"),
			Operator::Logical(ast::LogicalOp::Or)   => write!(f, "or"),
			Operator::Logical(ast::LogicalOp::Nand) => write!(f, "nand"),
			Operator::Logical(ast::LogicalOp::Nor)  => write!(f, "nor"),
			Operator::Logical(ast::LogicalOp::Xor)  => write!(f, "xor"),
			Operator::Logical(ast::LogicalOp::Xnor) => write!(f, "xnor"),
			Operator::Rel(ast::RelationalOp::Eq)    => write!(f, "="),
			Operator::Rel(ast::RelationalOp::Neq)   => write!(f, "/="),
			Operator::Rel(ast::RelationalOp::Lt)    => write!(f, "<"),
			Operator::Rel(ast::RelationalOp::Leq)   => write!(f, "<="),
			Operator::Rel(ast::RelationalOp::Gt)    => write!(f, ">"),
			Operator::Rel(ast::RelationalOp::Geq)   => write!(f, ">="),
			Operator::Match(ast::RelationalOp::Eq)  => write!(f, "?="),
			Operator::Match(ast::RelationalOp::Neq) => write!(f, "?/="),
			Operator::Match(ast::RelationalOp::Lt)  => write!(f, "?<"),
			Operator::Match(ast::RelationalOp::Leq) => write!(f, "?<="),
			Operator::Match(ast::RelationalOp::Gt)  => write!(f, "?>"),
			Operator::Match(ast::RelationalOp::Geq) => write!(f, "?>="),
			Operator::Shift(ast::ShiftOp::Sll)      => write!(f, "sll"),
			Operator::Shift(ast::ShiftOp::Srl)      => write!(f, "srl"),
			Operator::Shift(ast::ShiftOp::Sla)      => write!(f, "sla"),
			Operator::Shift(ast::ShiftOp::Sra)      => write!(f, "sra"),
			Operator::Shift(ast::ShiftOp::Rol)      => write!(f, "rol"),
			Operator::Shift(ast::ShiftOp::Ror)      => write!(f, "ror"),
			Operator::Add                           => write!(f, "+"),
			Operator::Sub                           => write!(f, "-"),
			Operator::Concat                        => write!(f, "&"),
			Operator::Mul                           => write!(f, "*"),
			Operator::Div                           => write!(f, "/"),
			Operator::Mod                           => write!(f, "mod"),
			Operator::Rem                           => write!(f, "rem"),
			Operator::Pow                           => write!(f, "**"),
			Operator::Abs                           => write!(f, "abs"),
			Operator::Not                           => write!(f, "not"),
		}
	}
}


// Declare the node references.
node_ref!(ArchRef);
node_ref!(BuiltinPkgRef);
node_ref!(CfgRef);
node_ref!(CtxItemsRef);
node_ref!(CtxRef);
node_ref!(DesignUnitRef);
node_ref!(EntityRef);
node_ref!(ExprRef);
node_ref!(IntfConstRef);
node_ref!(IntfPkgRef);
node_ref!(IntfSignalRef);
node_ref!(IntfSubprogRef);
node_ref!(IntfTypeRef);
node_ref!(LibRef);
node_ref!(PkgBodyRef);
node_ref!(PkgDeclRef);
node_ref!(PkgInstRef);
node_ref!(SubtypeIndRef);

// Declare the node reference groups.
node_ref_group!(Def:
	Arch(ArchRef),
	Cfg(CfgRef),
	Ctx(CtxRef),
	Entity(EntityRef),
	Lib(LibRef),
	Pkg(PkgDeclRef),
	PkgInst(PkgInstRef),
	BuiltinPkg(BuiltinPkgRef),
);
node_ref_group!(ScopeRef:
	Lib(LibRef),
	CtxItems(CtxItemsRef),
	Entity(EntityRef),
	BuiltinPkg(BuiltinPkgRef),
);
node_ref_group!(GenericRef:
	Type(IntfTypeRef),
	Subprog(IntfSubprogRef),
	Pkg(IntfPkgRef),
	Const(IntfConstRef),
);


// Declare the node tables.
node_storage!(AstTable<'ast>,
	subtys: SubtypeIndRef => (ScopeRef, &'ast ast::SubtypeInd),
	ctx_items: CtxItemsRef => (ScopeRef, &'ast [ast::CtxItem]),

	// The design units are tuples that also carry the list of context items
	// that were defined before them.
	entity_decls: EntityRef  => (LibRef, CtxItemsRef, &'ast ast::EntityDecl),
	cfg_decls:    CfgRef     => (LibRef, CtxItemsRef, &'ast ast::CfgDecl),
	pkg_decls:    PkgDeclRef => (LibRef, CtxItemsRef, &'ast ast::PkgDecl),
	pkg_insts:    PkgInstRef => (LibRef, CtxItemsRef, &'ast ast::PkgInst),
	ctx_decls:    CtxRef     => (LibRef, CtxItemsRef, &'ast ast::CtxDecl),
	arch_bodies:  ArchRef    => (LibRef, CtxItemsRef, &'ast ast::ArchBody),
	pkg_bodies:   PkgBodyRef => (LibRef, CtxItemsRef, &'ast ast::PkgBody),

	// Interface declarations
	intf_sigs:       IntfSignalRef      => (NodeId, &'ast ast::IntfObjDecl, SubtypeIndRef, &'ast ast::Ident),
	intf_types:      IntfTypeRef        => (NodeId, &'ast ast::TypeDecl),
	intf_subprogs:   IntfSubprogRef     => (NodeId, &'ast ast::IntfSubprogDecl),
	intf_pkgs:       IntfPkgRef         => (NodeId, &'ast ast::PkgInst),
	intf_consts:     IntfConstRef       => (NodeId, &'ast ast::IntfObjDecl, SubtypeIndRef, &'ast ast::Ident),

	exprs: ExprRef => (NodeId, &'ast ast::Expr),
);

node_storage!(HirTable<'ctx>,
	libs:         LibRef        => &'ctx hir::Lib,
	entities:     EntityRef     => &'ctx hir::Entity,
	intf_sigs:    IntfSignalRef => &'ctx hir::IntfSignal,
	subtype_inds: SubtypeIndRef => &'ctx hir::SubtypeInd,
);


lazy_static! {
	/// A table of the scopes of all builtin packages.
	static ref BUILTIN_PKG_SCOPES: HashMap<BuiltinPkgRef, Scope> = {
		let mut scopes = HashMap::new();
		scopes.insert(*STANDARD_PKG_REF, Scope{
			parent: None,
			defs: vec![(*STANDARD_PKG_REF).into()],
		});
		scopes
	};

	/// A table of the definitions of all builtin packages.
	static ref BUILTIN_PKG_DEFS: HashMap<BuiltinPkgRef, Defs> = {
		let nt = get_name_table();
		let mut table = HashMap::new();
		table.insert(*STANDARD_PKG_REF, {
			let mut defs = HashMap::new();
			// TODO: Insert builtin definitions here.
			// defs.insert(
			// 	nt.intern("integer", false).into(),
			// 	vec![Spanned::new(Def::BuiltinTy(IntTy), INVALID_SPAN)]
			// );
			defs
		});
		table
	};
}
