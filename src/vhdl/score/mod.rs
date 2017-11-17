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
use konst::*;
use num::{BigInt, Signed};
use codegen::Codegen;


/// This macro implements the `NodeMaker` trait for a specific combination of
/// identifier and output type.
macro_rules! impl_make {
	($slf:tt, $id:ident: $id_ty:ty => &$out_ty:ty $blk:block) => {
		impl<'sb, 'ast, 'ctx> NodeMaker<$id_ty, &'ctx $out_ty> for ScoreContext<'sb, 'ast, 'ctx> {
			fn make(&$slf, $id: $id_ty) -> Result<&'ctx $out_ty> $blk
		}
	}
}

mod lower_hir;
mod typeck;
mod scope;
mod cval;


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
	ty_table: RefCell<HashMap<NodeId, &'ctx Ty>>,
	/// A table of scopes.
	scope_table: RefCell<HashMap<ScopeRef, &'ctx Scope>>,
	/// A table of nodes' constant values.
	const_table: RefCell<HashMap<NodeId, &'ctx Const>>,
	/// A table of type contexts for expressions.
	tyctx_table: RefCell<HashMap<NodeId, TypeCtx<'ctx>>>,
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
			const_table: RefCell::new(HashMap::new()),
			tyctx_table: RefCell::new(HashMap::new()),
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


	/// Obtain the HIR of a node, generating it if needed. Returns an error if
	/// the HIR cannot be generated.
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


	/// Obtain the HIR of a node. Returns an error if none exists.
	pub fn existing_hir<I>(&self, id: I) -> Result<<HirTable<'ctx> as NodeStorage<I>>::Node>
	where
		I: Copy + Debug,
		HirTable<'ctx>: NodeStorage<I>
	{
		match self.sb.hir_table.borrow().get(&id) {
			Some(node) => Ok(node),
			None => {
				self.sess.emit(DiagBuilder2::fatal(format!("hir for {:?} should exist", id)));
				Err(())
			}
		}
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


	pub fn ty<I>(&self, id: I) -> Result<&'ctx Ty>
	where
		I: 'ctx + Copy + Debug + Into<NodeId>,
		ScoreContext<'sb, 'ast, 'ctx>: NodeMaker<I, &'ctx Ty>
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


	pub fn const_value<I>(&self, id: I) -> Result<&'ctx Const>
	where
		I: 'ctx + Copy + Debug + Into<NodeId>,
		ScoreContext<'sb, 'ast, 'ctx>: NodeMaker<I, &'ctx Const>
	{
		if let Some(node) = self.sb.const_table.borrow().get(&id.into()).cloned() {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make const for {:?}", id); }
		let node = self.make(id)?;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] const for {:?} is {:?}", id, node); }
		if self.sb.const_table.borrow_mut().insert(id.into(), node).is_some() {
			panic!("node should not exist");
		}
		Ok(node)
	}


	/// Obtain the type context for an expression. Returns `None` if no context
	/// information is available.
	pub fn type_context<I>(&self, id: I) -> Option<TypeCtx<'ctx>>
	where I: Copy + Debug + Into<NodeId>
	{
		self.sb.tyctx_table.borrow().get(&id.into()).map(|&t| t)
	}


	/// Store a type context for an expression. Upon type checking, the
	/// expression is likely to consult this context to determine its type.
	pub fn set_type_context<I>(&self, id: I, tyctx: TypeCtx<'ctx>)
	where I: Copy + Debug + Into<NodeId>
	{
		self.sb.tyctx_table.borrow_mut().insert(id.into(), tyctx);
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
					self.set_ast(subid, (ctx_id.into(), decl));
					lib.pkg_decls.push(subid);
				}
				ast::DesignUnitData::PkgInst(ref decl) => {
					let subid = PkgInstRef(NodeId::alloc());
					self.set_ast(subid, (ctx_id.into(), decl));
					lib.pkg_insts.push(subid);
				}
				ast::DesignUnitData::CtxDecl(ref decl) => {
					let subid = CtxRef(NodeId::alloc());
					self.set_ast(subid, (id, ctx_id, decl));
					lib.ctxs.push(subid);
				}
				ast::DesignUnitData::ArchBody(ref decl) => {
					let subid = ArchRef(NodeId::alloc());
					self.set_ast(subid, (id, ctx_id.into(), decl));
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
			ctx_items: ctx_id,
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
		let (scope_id, decl, subty_id, ident) = self.ast(id);
		let init = match decl.default {
			Some(ref e) => {
				let subid = ExprRef(NodeId::alloc());
				self.set_ast(subid, (scope_id, e));
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
	pub fn resolve_name(&self, name: Spanned<ResolvableName>, scope_id: ScopeRef, only_defs: bool) -> Result<Vec<Spanned<Def>>> {
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] resolve {:?} in scope {:?}", name.value, scope_id); }
		let mut found_defs = Vec::new();
		let parent_id = if only_defs {
			let defs = self.defs(scope_id)?;
			if let Some(d) = defs.get(&name.value) {
				found_defs.extend(d);
			}
			None
		} else {
			let scope = self.scope(scope_id)?;
			for &defs_id in &scope.defs {
				let defs = self.defs(defs_id)?;
				if let Some(d) = defs.get(&name.value) {
					found_defs.extend(d);
				}
			}
			scope.parent
		};

		// If nothing matched the definition, try to escalate to the parent
		// scope. If there is no parent scope, i.e. we're the parent, fail with
		// a diagnostic.
		if found_defs.is_empty() {
			if let Some(parent_id) = parent_id {
				self.resolve_name(name, parent_id, only_defs)
			} else {
				self.sess.emit(DiagBuilder2::error(format!("`{}` is not known", name.value)).span(name.span));
				Err(())
			}
		} else {
			if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] resolved {:?} to {:?}", name.value, found_defs); }
			Ok(found_defs)
		}
	}


	pub fn resolve_compound_name<'a>(&self, name: &'a ast::CompoundName, scope_id: ScopeRef, only_defs: bool) -> Result<(ResolvableName, Vec<Spanned<Def>>, Span, &'a [ast::NamePart])> {
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] resolve compound {:?} in scope {:?}", name, scope_id); }

		// First resolve the primary name.
		let mut seen_span = name.primary.span;
		let mut res_name = self.resolvable_from_primary_name(&name.primary)?;
		let mut defs = self.resolve_name(res_name, scope_id, only_defs)?;

		// Resolve as many name parts as possible.
		for i in 0..name.parts.len() {
			match name.parts[i] {
				ast::NamePart::Select(ref pn) => {
					// Ensure that we only have one definition, i.e. that the
					// name up to this point is not ambiguous.
					let def = if defs.len() == 1 {
						defs[0]
					} else {
						let span_str = seen_span.extract();
						let mut d = DiagBuilder2::error(format!("`{}` is ambiguous", span_str))
							.span(seen_span)
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
						Def::Pkg(id) => id.into(),
						Def::PkgInst(id) => id.into(),
						Def::BuiltinPkg(id) => id.into(),
						d => {
							self.sess.emit(
								DiagBuilder2::error(format!("cannot select into {:?}", d))
								.span(pn.span)
							);
							return Err(());
						}
					};

					// Perform the name resolution in the scope determined
					// above.
					seen_span.expand(pn.span);
					res_name = self.resolvable_from_primary_name(pn)?;
					defs = self.resolve_name(res_name, scope, true)?;
				}

				// All other name parts we do not resolve and simply pass back
				// to the caller.
				_ => return Ok((res_name.value, defs, seen_span, &name.parts[i..]))
			}
		}

		// If we arrive here, we were able to resolve the entire name. So we
		// simply return the definitions found and an empty slice of remaining
		// parts.
		Ok((res_name.value, defs, seen_span, &[]))
	}
}


// Lower a package declaration to HIR.
impl<'sb, 'ast, 'ctx> NodeMaker<PkgDeclRef, &'ctx hir::Package> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: PkgDeclRef) -> Result<&'ctx hir::Package> {
		let (scope_id, ast) = self.ast(id);
		let generics = Vec::new();
		// let generic_maps = Vec::new();
		let mut decls = Vec::new();
		let mut had_fails = false;

		// Filter the declarations in the package to only those that we actually
		// support, and separate the generic clauses and maps.
		for decl in &ast.decls {
			match *decl {
				ast::DeclItem::PkgDecl(ref decl) => {
					let subid = PkgDeclRef(NodeId::alloc());
					self.set_ast(subid, (id.into(), decl));
					decls.push(subid.into());
				}
				ast::DeclItem::PkgInst(ref decl) => {
					let subid = PkgInstRef(NodeId::alloc());
					self.set_ast(subid, (id.into(), decl));
					decls.push(subid.into());
				}
				ast::DeclItem::TypeDecl(ref decl) => {
					let subid = TypeDeclRef(NodeId::alloc());
					self.set_ast(subid, (id.into(), decl));
					decls.push(subid.into());
				}
				ast::DeclItem::SubtypeDecl(ref decl) => {
					let subid = SubtypeDeclRef(NodeId::alloc());
					self.set_ast(subid, (id.into(), decl));
					decls.push(subid.into());
				}

				// Emit an error for any other kinds of declarations.
				ref wrong => {
					self.sess.emit(
						DiagBuilder2::error(format!("A {} cannot appear in a package declaration", wrong.desc()))
						.span(decl.human_span())
					);
					had_fails = true;
					continue;
				}
			}
		}

		if had_fails {
			Err(())
		} else {
			Ok(self.sb.arenas.hir.package.alloc(hir::Package{
				parent: scope_id,
				name: ast.name,
				generics: generics,
				decls: decls,
			}))
		}
	}
}


impl<'sb, 'ast, 'ctx> ScoreContext<'sb, 'ast, 'ctx> {
	/// Unpack a slice of AST declarative items into a list of items admissible
	/// in the declarative part of a block. See IEEE 1076-2008 section 3.3.2.
	fn unpack_block_decls(&self, scope_id: ScopeRef, decls: &'ast [ast::DeclItem], container_name: &str) -> Result<Vec<DeclInBlockRef>> {
		let mut refs = Vec::new();
		let mut had_fails = false;

		for decl in decls {
			match *decl {
				ast::DeclItem::PkgDecl(ref decl) => {
					let subid = PkgDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::PkgInst(ref decl) => {
					let subid = PkgInstRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::TypeDecl(ref decl) => {
					let subid = TypeDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::SubtypeDecl(ref decl) => {
					let subid = SubtypeDeclRef(NodeId::alloc());
					self.set_ast(subid, (scope_id, decl));
					refs.push(subid.into());
				}
				ast::DeclItem::ObjDecl(ref decl) => {
					match decl.kind {
						ast::ObjKind::Const => {
							let subid = ConstDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::ObjKind::Signal => self.unpack_signal_decl(decl, scope_id, &mut refs)?,
						ast::ObjKind::Var => {
							self.sess.emit(
								DiagBuilder2::error(format!("Not a shared variable; only shared variables may appear in {}", container_name))
								.span(decl.human_span())
							);
							had_fails = true;
						}
						ast::ObjKind::SharedVar => {
							let subid = SharedVariableDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
						ast::ObjKind::File => {
							let subid = FileDeclRef(NodeId::alloc());
							self.set_ast(subid, (scope_id, decl));
							refs.push(subid.into());
						}
					}
				}

				// Emit an error for any other kinds of declarations.
				ref wrong => {
					self.sess.emit(
						DiagBuilder2::error(format!("A {} cannot appear in {}", wrong.desc(), container_name))
						.span(decl.human_span())
					);
					had_fails = true;
				}
			}
		}

		if had_fails {
			Err(())
		} else {
			Ok(refs)
		}
	}


	/// Unpack a slice of AST concurrent statements. See IEEE 1076-2008 section
	/// 11.1.
	fn unpack_concurrent_stmts(&self, _scope_id: ScopeRef, stmts: &'ast [ast::Stmt], container_name: &str) -> Result<Vec<ConcStmtRef>> {
		let refs = Vec::new();
		let mut had_fails = false;

		for stmt in stmts {
			match stmt.data {

				// Emit an error for any other kinds of declarations.
				_ => {
					self.sess.emit(
						DiagBuilder2::error(format!("A {} cannot appear in {}", stmt.desc(), container_name))
						.span(stmt.human_span())
						.add_note(format!("Only concurrent statements are allowed in {}. See IEEE 1076-2008 section 11.1.", container_name))
					);
					had_fails = true;
					continue;
				}
			}
		}

		if had_fails {
			Err(())
		} else {
			Ok(refs)
		}
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
	fn make(&self, _: ArchRef) -> Result<DeclValueRef> {
		unimplemented!();
	}
}


// Generate the definition for an architecture.
impl<'sb, 'ast, 'ctx> NodeMaker<ArchRef, DefValueRef> for ScoreContext<'sb, 'ast, 'ctx> {
	fn make(&self, id: ArchRef) -> Result<DefValueRef> {
		let hir = self.hir(id)?;
		let entity = self.hir(hir.entity)?;

		// Assemble the types and names for the entity.
		println!("entity ports: {:?}", entity.ports);
		let mut in_tys    = Vec::new();
		let mut out_tys   = Vec::new();
		let mut in_names  = Vec::new();
		let mut out_names = Vec::new();
		for &port in &entity.ports {
			let hir = self.hir(port)?;
			let ty = self.map_type(self.ty(hir.ty)?)?;
			// let ty = llhd::void_ty();
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
		let ty = llhd::entity_ty(in_tys, out_tys);

		// Create a new entity into which we will generate all the code.
		let name = format!("{}_{}", entity.name.value, hir.name.value);
		let mut entity = llhd::Entity::new(name, ty);

		// Assign names to the arguments. This is merely cosmetic, but makes the
		// emitted LLHD easier to read.
		for (arg, &name) in entity.inputs_mut().iter_mut().zip(in_names.iter()) {
			arg.set_name(name.as_str().to_owned());
		}
		for (arg, &name) in entity.outputs_mut().iter_mut().zip(out_names.iter()) {
			arg.set_name(name.as_str().to_owned());
		}

		// Generate the code for the declarations in the architecture.
		for &decl_id in &hir.decls {
			self.codegen(decl_id, &mut entity)?;
		}

		// Add the entity to the module and return a reference to it.
		Ok(DefValueRef(self.sb.llmod.borrow_mut().add_entity(entity).into()))
	}
}


impl<'sb, 'ast, 'ctx> ScoreContext<'sb, 'ast, 'ctx> {
	/// Calculate the implicit default value for a type.
	pub fn default_value_for_type(&self, ty: &Ty) -> Result<&'ctx Const> {
		match *ty {
			Ty::Named(_, ty) => self.default_value_for_type(self.ty(ty)?),
			Ty::Null => Ok(self.intern_const(Const::Null)),
			Ty::Enum(ref _ty) => {
				// TODO: Replace with the first literal in the enum.
				Ok(self.intern_const(Const::Null))
			}
			Ty::Int(ref ty) => Ok(self.intern_const(ConstInt::new(Some(ty.clone()), ty.left_bound.clone()))),
			Ty::UnboundedInt => panic!("unbounded integer has no default value"),
		}
	}


	/// Internalize the given constant and return a reference to it whose
	/// lifetime is bound to the arenas associated with the scoreboard.
	pub fn intern_const<T>(&self, konst: T) -> &'ctx Const where T: Into<Const> {
		self.sb.arenas.konst.alloc(konst.into())
	}


	/// Internalize the given type and return a reference to it whose lifetime
	/// is bound to the arenas associated with the scoreboard.
	pub fn intern_ty<T>(&self, ty: T) -> &'ctx Ty where T: Into<Ty> {
		self.sb.arenas.ty.alloc(ty.into())
	}
}


/// A collection of arenas that the scoreboard uses to allocate its nodes.
pub struct Arenas {
	pub hir: hir::Arenas,
	pub defs: Arena<Defs>,
	pub archs: Arena<ArchTable>,
	pub scope: Arena<Scope>,
	pub ty: Arena<Ty>,
	pub konst: Arena<Const>,
}


impl Arenas {
	/// Create a new set of arenas.
	pub fn new() -> Arenas {
		Arenas {
			hir: hir::Arenas::new(),
			defs: Arena::new(),
			archs: Arena::new(),
			scope: Arena::new(),
			ty: Arena::new(),
			konst: Arena::new(),
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
	/// Additional explicitly imported definitions.
	pub explicit_defs: Defs,
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

impl From<char> for ResolvableName {
	fn from(c: char) -> ResolvableName {
		ResolvableName::Bit(c)
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


/// The type requirements imposed upon an expression by its context. This is
/// needed for overload resolution, where the type of the overload to be picked
/// is determined by the context in which the expression appears.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TypeCtx<'ctx> {
	/// The exact type the expression must have.
	Type(&'ctx Ty),
	/// The node whose type the expression must match.
	TypeOf(TypedNodeRef),
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
node_ref!(TypeDeclRef);
node_ref!(SubtypeDeclRef);
node_ref!(WaitStmtRef);
node_ref!(AssertStmtRef);
node_ref!(ReportStmtRef);
node_ref!(SigAssignStmtRef);
node_ref!(VarAssignStmtRef);
node_ref!(ProcCallStmtRef);
node_ref!(IfStmtRef);
node_ref!(CaseStmtRef);
node_ref!(LoopStmtRef);
node_ref!(NextStmtRef);
node_ref!(ExitStmtRef);
node_ref!(ReturnStmtRef);
node_ref!(NullStmtRef);
node_ref!(BlockStmtRef);
node_ref!(ProcessStmtRef);
node_ref!(ConcProcCallStmtRef);
node_ref!(ConcAssertStmtRef);
node_ref!(ConcSigAssignStmtRef);
node_ref!(CompInstStmtRef);
node_ref!(ForGenStmtRef);
node_ref!(IfGenStmtRef);
node_ref!(CaseGenStmtRef);
node_ref!(ConstDeclRef);
node_ref!(SignalDeclRef);
node_ref!(VariableDeclRef);
node_ref!(SharedVariableDeclRef);
node_ref!(FileDeclRef);

/// A reference to an enumeration literal, expressed as the type declaration
/// which defines the enumeration and the index of the literal.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, RustcEncodable, RustcDecodable, Hash, Debug)]
pub struct EnumRef(pub TypeDeclRef, pub usize);

impl Into<NodeId> for EnumRef {
	fn into(self) -> NodeId {
		panic!("EnumRef cannot be converted into a NodeId");
	}
}

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
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
	Enum(EnumRef),
);
node_ref_group!(ScopeRef:
	Lib(LibRef),
	CtxItems(CtxItemsRef),
	Entity(EntityRef),
	BuiltinPkg(BuiltinPkgRef),
	Pkg(PkgDeclRef),
	PkgInst(PkgInstRef),
	Arch(ArchRef),
);
node_ref_group!(GenericRef:
	Type(IntfTypeRef),
	Subprog(IntfSubprogRef),
	Pkg(IntfPkgRef),
	Const(IntfConstRef),
);

node_ref_group!(TypeMarkRef:
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
);

/// All declarations that may possibly appear in a package. See IEEE 1076-2008
/// section 4.7.
///
/// ```text
/// subprogram_declaration
/// subprogram_instantiation_declaration
/// package_declaration
/// package_instantiation_declaration
/// type_declaration
/// subtype_declaration
/// constant_declaration
/// signal_declaration
/// variable_declaration
/// file_declaration
/// alias_declaration
/// component_declaration
/// attribute_declaration
/// attribute_specification
/// disconnection_specification
/// use_clause
/// group_template_declaration
/// group_declaration
/// ```
node_ref_group!(DeclInPkgRef:
	Pkg(PkgDeclRef),
	PkgInst(PkgInstRef),
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
);

/// All declarations that may possibly appear in a block. See IEEE 1076-2008
/// section 3.3.2.
///
/// ```text
/// subprogram_declaration
/// subprogram_body
/// subprogram_instantiation_declaration
/// package_declaration
/// package_body
/// package_instantiation_declaration
/// type_declaration
/// subtype_declaration
/// constant_declaration
/// signal_declaration
/// shared_variable_declaration
/// file_declaration
/// alias_declaration
/// component_declaration
/// attribute_declaration
/// attribute_specification
/// configuration_specification
/// disconnection_specification
/// use_clause
/// group_template_declaration
/// group_declaration
/// ```
node_ref_group!(DeclInBlockRef:
	Pkg(PkgDeclRef),
	PkgInst(PkgInstRef),
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
	Const(ConstDeclRef),
	Signal(SignalDeclRef),
	SharedVariable(SharedVariableDeclRef),
	File(FileDeclRef),
);

/// All concurrent statements. See IEEE 1076-2008 section 11.1.
///
/// ```text
/// block_statement
/// process_statement
/// concurrent_procedure_call_statement
/// concurrent_assertion_statement
/// concurrent_signal_assignment_statement
/// component_instantiation_statement
/// generate_statement
/// ```
node_ref_group!(ConcStmtRef:
	Block(BlockStmtRef),
	Process(ProcessStmtRef),
	ConcProcCall(ConcProcCallStmtRef),
	ConcAssert(ConcAssertStmtRef),
	ConcSigAssign(ConcSigAssignStmtRef),
	CompInst(CompInstStmtRef),
	ForGen(ForGenStmtRef),
	IfGen(IfGenStmtRef),
	CaseGen(CaseGenStmtRef),
);

/// All sequential statements. See IEEE 1076-2008 section 10.1.
///
/// ```text
/// wait_statement
/// assertion_statement
/// report_statement
/// signal_assignment_statement
/// variable_assignment_statement
/// procedure_call_statement
/// if_statement
/// case_statement
/// loop_statement
/// next_statement
/// exit_statement
/// return_statement
/// null_statement
/// ```
node_ref_group!(SeqStmtRef:
	Wait(WaitStmtRef),
	Assert(AssertStmtRef),
	Report(ReportStmtRef),
	SigAssign(SigAssignStmtRef),
	VarAssign(VarAssignStmtRef),
	ProcCall(ProcCallStmtRef),
	If(IfStmtRef),
	Case(CaseStmtRef),
	Loop(LoopStmtRef),
	Next(NextStmtRef),
	Exit(ExitStmtRef),
	Return(ReturnStmtRef),
	Null(NullStmtRef),
);

/// A reference to a node which has a type.
node_ref_group!(TypedNodeRef:
	SubtypeInd(SubtypeIndRef),
);


// Declare the node tables.
node_storage!(AstTable<'ast>,
	subtys: SubtypeIndRef => (ScopeRef, &'ast ast::SubtypeInd),
	ctx_items: CtxItemsRef => (ScopeRef, &'ast [ast::CtxItem]),

	// The design units are tuples that also carry the list of context items
	// that were defined before them.
	entity_decls: EntityRef  => (LibRef, CtxItemsRef, &'ast ast::EntityDecl),
	cfg_decls:    CfgRef     => (LibRef, CtxItemsRef, &'ast ast::CfgDecl),
	pkg_decls:    PkgDeclRef => (ScopeRef, &'ast ast::PkgDecl),
	pkg_insts:    PkgInstRef => (ScopeRef, &'ast ast::PkgInst),
	ctx_decls:    CtxRef     => (LibRef, CtxItemsRef, &'ast ast::CtxDecl),
	arch_bodies:  ArchRef    => (LibRef, CtxItemsRef, &'ast ast::ArchBody),
	pkg_bodies:   PkgBodyRef => (LibRef, CtxItemsRef, &'ast ast::PkgBody),

	// Interface declarations
	intf_sigs:       IntfSignalRef      => (ScopeRef, &'ast ast::IntfObjDecl, SubtypeIndRef, &'ast ast::Ident),
	intf_types:      IntfTypeRef        => (ScopeRef, &'ast ast::TypeDecl),
	intf_subprogs:   IntfSubprogRef     => (ScopeRef, &'ast ast::IntfSubprogDecl),
	intf_pkgs:       IntfPkgRef         => (ScopeRef, &'ast ast::PkgInst),
	intf_consts:     IntfConstRef       => (ScopeRef, &'ast ast::IntfObjDecl, SubtypeIndRef, &'ast ast::Ident),

	// Declarations
	type_decls:            TypeDeclRef           => (ScopeRef, &'ast ast::TypeDecl),
	subtype_decls:         SubtypeDeclRef        => (ScopeRef, &'ast ast::SubtypeDecl),
	const_decls:           ConstDeclRef          => (ScopeRef, &'ast ast::ObjDecl),
	signal_decls:          SignalDeclRef         => (ScopeRef, &'ast ast::ObjDecl),
	variable_decls:        VariableDeclRef       => (ScopeRef, &'ast ast::ObjDecl),
	shared_variable_decls: SharedVariableDeclRef => (ScopeRef, &'ast ast::ObjDecl),
	file_decls:            FileDeclRef           => (ScopeRef, &'ast ast::ObjDecl),

	exprs: ExprRef => (ScopeRef, &'ast ast::Expr),
);

node_storage!(HirTable<'ctx>,
	libs:                  LibRef                => &'ctx hir::Lib,
	entities:              EntityRef             => &'ctx hir::Entity,
	archs:                 ArchRef               => &'ctx hir::Arch,
	intf_sigs:             IntfSignalRef         => &'ctx hir::IntfSignal,
	subtype_inds:          SubtypeIndRef         => &'ctx hir::SubtypeInd,
	pkgs:                  PkgDeclRef            => &'ctx hir::Package,
	type_decls:            TypeDeclRef           => &'ctx hir::TypeDecl,
	subtype_decls:         SubtypeDeclRef        => &'ctx hir::SubtypeDecl,
	exprs:                 ExprRef               => &'ctx hir::Expr,
	const_decls:           ConstDeclRef          => &'ctx hir::ConstDecl,
	signal_decls:          SignalDeclRef         => &'ctx hir::SignalDecl,
	variable_decls:        VariableDeclRef       => &'ctx hir::VariableDecl,
	shared_variable_decls: SharedVariableDeclRef => &'ctx hir::VariableDecl,
	file_decls:            FileDeclRef           => &'ctx hir::FileDecl,
);


lazy_static! {
	/// A table of the scopes of all builtin packages.
	static ref BUILTIN_PKG_SCOPES: HashMap<BuiltinPkgRef, Scope> = {
		let mut scopes = HashMap::new();
		scopes.insert(*STANDARD_PKG_REF, Scope{
			parent: None,
			defs: vec![(*STANDARD_PKG_REF).into()],
			explicit_defs: HashMap::new(),
		});
		scopes
	};

	/// A table of the definitions of all builtin packages.
	static ref BUILTIN_PKG_DEFS: HashMap<BuiltinPkgRef, Defs> = {
		// let nt = get_name_table();
		let mut table = HashMap::new();
		table.insert(*STANDARD_PKG_REF, {
			let defs = HashMap::new();
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
