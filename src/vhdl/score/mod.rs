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
use moore_common::util::{HasSpan, HasDesc};

use typed_arena::Arena;
use num::{BigInt, Signed};
use llhd;

use syntax::ast;
use hir;
use ty::*;
use konst::*;
use codegen::Codegen;
use typeck::{Typeck, TypeckContext};
use lazy::*;
use arenas::Alloc;


/// This macro implements the `NodeMaker` trait for a specific combination of
/// identifier and output type.
macro_rules! impl_make {
	($slf:tt, $id:ident: $id_ty:ty => &$out_ty:ty $blk:block) => {
		impl<'lazy, 'sb, 'ast, 'ctx> NodeMaker<$id_ty, &'ctx $out_ty> for ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
			fn make(&$slf, $id: $id_ty) -> Result<&'ctx $out_ty> $blk
		}
	};
	($slf:tt, $id:ident: $id_ty:ty => $out_ty:ty $blk:block) => {
		impl<'lazy, 'sb, 'ast, 'ctx> NodeMaker<$id_ty, $out_ty> for ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
			fn make(&$slf, $id: $id_ty) -> Result<$out_ty> $blk
		}
	}
}

mod lower_hir;
mod scope;
mod cval;


/// The VHDL context which holds information about the language scoreboard and
/// the global scoreboard in its language-agnostic generic form. All useful
/// operations are defined on this context rather than on the scoreboard
/// directly, to decouple processing and ownership.
pub struct ScoreContext<'lazy, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb> {
	/// The compiler session which carries the options and is used to emit
	/// diagnostics.
	pub sess: &'lazy Session,
	/// The global context.
	pub global: &'lazy GenericContext,
	/// The VHDL scoreboard.
	pub sb: &'sb ScoreBoard<'ast, 'ctx>,
	/// The table of scheduled operations.
	pub lazy: &'lazy LazyPhaseTable<'sb, 'ast, 'ctx>,
}


/// The VHDL scoreboard that keeps track of compilation results.
pub struct ScoreBoard<'ast, 'ctx> {
	/// A reference to the arenas where the scoreboard allocates nodes.
	pub arenas: &'ctx Arenas,
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
	/// A table of typeck results.
	pub typeck_table: RefCell<HashMap<NodeId, Result<()>>>,
	/// A table of typeval results.
	pub typeval_table: RefCell<HashMap<NodeId, Result<&'ctx Ty>>>,
	/// Emit note for each AST node converted to a term.
	trace_termification: bool,
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
			typeck_table: RefCell::new(HashMap::new()),
			typeval_table: RefCell::new(HashMap::new()),
			trace_termification: false,
		}
	}
}


impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
	/// Emit a diagnostic message.
	pub fn emit(&self, diag: DiagBuilder2) {
		self.sess.emit(diag)
	}

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
			Some(&node) => node,
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
		ScoreContext<'lazy, 'sb, 'ast, 'ctx>: NodeMaker<I, <HirTable<'ctx> as NodeStorage<I>>::Node>,
		<HirTable<'ctx> as NodeStorage<I>>::Node: Copy + Debug {

		if let Some(&node) = self.sb.hir_table.borrow().get(&id) {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make hir for {:?}", id); }
		let node = self.make(id)?;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] hir for {:?} is {:?}", id, node); }
		self.set_hir(id, node);
		Ok(node)
	}


	/// Store the HIR of a node.
	pub fn set_hir<I>(&self, id: I, hir: <HirTable<'ctx> as NodeStorage<I>>::Node)
	where
		I: Copy + Debug,
		HirTable<'ctx>: NodeStorage<I>
	{
		self.sb.hir_table.borrow_mut().set(id, hir);
	}

	/// Obtain the HIR of a node. Returns an error if none exists.
	pub fn existing_hir<I>(&self, id: I) -> Result<<HirTable<'ctx> as NodeStorage<I>>::Node>
	where
		I: Copy + Debug,
		HirTable<'ctx>: NodeStorage<I>,
		<HirTable<'ctx> as NodeStorage<I>>::Node: Copy + Debug,
	{
		match self.sb.hir_table.borrow().get(&id) {
			Some(&node) => Ok(node),
			None => {
				self.emit(DiagBuilder2::bug(format!("hir for {:?} should exist", id)));
				Err(())
			}
		}
	}

	/// Determine the HIR for a node.
	///
	/// If the HIR is already in the scoreboard, returns it immediately.
	/// Otherwise the lazy HIR table is triggered which will compute the HIR via
	/// the corresponding closure.
	pub fn lazy_hir<I,R>(&self, id: I) -> Result<&'ctx R>
	where
		I: Copy + Debug,
		R: Debug + 'ctx,
		LazyHirTable<'sb, 'ast, 'ctx>: NodeStorage<I, Node=LazyNode<Box<for<'a,'b> Fn(&'a ScoreContext<'b, 'sb, 'ast, 'ctx>) -> Result<R> + 'sb>>>,
		HirTable<'ctx>: NodeStorage<I, Node=&'ctx R>,
		hir::Arenas: Alloc<R>,
	{
		// If the HIR has already been determined, return it immediately.
		if let Some(&node) = self.sb.hir_table.borrow().get(&id) {
			return Ok(node);
		}

		// Otherwise run the task scheduled in the lazy HIR table, then store
		// the result.
		let hir = self.lazy.hir.run(id, self)?;
		let allocd = self.sb.arenas.hir.alloc(hir);
		self.sb.hir_table.borrow_mut().set(id, allocd);

		Ok(allocd)
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
		ScoreContext<'lazy, 'sb, 'ast, 'ctx>: NodeMaker<I, DeclValueRef>
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
		ScoreContext<'lazy, 'sb, 'ast, 'ctx>: NodeMaker<I, DefValueRef>
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

	/// Determine the type of a node.
	///
	/// If called for the first time with the given `id`, calculates the type by
	/// calling `self.make(id)`. Otherwise returns the existing information.
	pub fn ty<I>(&self, id: I) -> Result<&'ctx Ty>
	where
		I: 'ctx + Copy + Debug + Into<NodeId>,
		ScoreContext<'lazy, 'sb, 'ast, 'ctx>: NodeMaker<I, &'ctx Ty>
	{
		if let Some(node) = self.sb.ty_table.borrow().get(&id.into()).cloned() {
			return Ok(node);
		}
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] make ty for {:?}", id); }
		let node = self.make(id)?;
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] ty for {:?} is {:?}", id, node); }
		if self.sb.ty_table.borrow_mut().insert(id.into(), node).is_some() {
			self.emit(
				DiagBuilder2::bug(format!("type for {:?} already in the scoreboard", id))
			);
			return Err(());
		}
		Ok(node)
	}

	/// Check the type of a node.
	///
	/// If the node already had its type checked, immediately returns the result
	/// of that operation. Otherwise runs the task scheduled in the lazy table.
	pub fn lazy_typeck<I>(&self, id: I) -> Result<()> where I: Into<NodeId> {
		let ctx = TypeckContext::new(self);
		ctx.lazy_typeck(id);
		if ctx.finish() {
			Ok(())
		} else {
			Err(())
		}
	}

	/// Determine the type of a node.
	///
	/// If the node already had its type determined, immediately returns the
	/// result of that operation. Otherwise runs the task scheduled in the lazy
	/// table.
	pub fn lazy_typeval<I>(&self, id: I) -> Result<&'ctx Ty> where I: Into<NodeId> {
		let ctx = TypeckContext::new(self);
		let result = ctx.lazy_typeval(id);
		if ctx.finish() {
			result
		} else {
			Err(())
		}
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
		ScoreContext<'lazy, 'sb, 'ast, 'ctx>: NodeMaker<I, &'ctx Const>
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


	/// Obtain the type context for an expression.
	///
	/// Returns `None` if no context information is available.
	pub fn type_context<I>(&self, id: I) -> Option<TypeCtx<'ctx>>
	where I: Copy + Debug + Into<NodeId>
	{
		self.sb.tyctx_table.borrow().get(&id.into()).map(|&t| t)
	}

	/// Obtain the type indicated by the type context for an expression.
	///
	/// Returns `None` if no context information is available.
	pub fn type_context_resolved<I>(&self, id: I) -> Result<Option<&'ctx Ty>>
	where I: Copy + Debug + Into<NodeId>
	{
		Ok(match self.type_context(id) {
			Some(TypeCtx::Type(t)) => Some(t),
			Some(TypeCtx::TypeOf(id)) => Some(self.ty(id)?),
			None => None,
		})
	}

	/// Store a type context for an expression.
	///
	/// Upon type checking, the expression is likely to consult this context to
	/// determine its type.
	pub fn set_type_context<I,T>(&self, id: I, tyctx: T)
		where I: Copy + Debug + Into<NodeId>, TypeCtx<'ctx>: From<T>
	{
		self.sb.tyctx_table.borrow_mut().insert(id.into(), tyctx.into());
	}

	/// Store a type context for an optional expression.
	///
	/// Upon type checking, the expression is likely to consult this context to
	/// determine its type. Does nothing if `id.is_none()`.
	pub fn set_type_context_optional<I,T>(&self, id: Option<I>, tyctx: T)
		where I: Copy + Debug + Into<NodeId>, TypeCtx<'ctx>: From<T>
	{
		match id {
			Some(id) => self.set_type_context(id, tyctx),
			None => (),
		}
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
impl<'lazy, 'sb, 'ast, 'ctx> NodeMaker<LibRef, &'ctx hir::Lib> for ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
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
					self.set_ast(subid, (ctx_id.into(), decl));
					lib.pkg_bodies.push(subid);
				}
			}
		}
		Ok(self.sb.arenas.hir.lib.alloc(lib))
	}
}


impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
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
						self.emit(
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
	pub fn resolve_name(&self, name: Spanned<ResolvableName>, scope_id: ScopeRef, only_defs: bool, allow_fail: bool) -> Result<Vec<Spanned<Def>>> {
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
			if let Some(d) = scope.explicit_defs.get(&name.value) {
				found_defs.extend(d.iter());
			}
			scope.parent
		};

		// If nothing matched the definition, try to escalate to the parent
		// scope. If there is no parent scope, i.e. we're the parent, fail with
		// a diagnostic.
		if found_defs.is_empty() {
			if let Some(parent_id) = parent_id {
				self.resolve_name(name, parent_id, only_defs, allow_fail)
			} else if allow_fail {
				Ok(vec![])
			} else {
				self.emit(DiagBuilder2::error(format!("`{}` is not known", name.value)).span(name.span));
				Err(())
			}
		} else {
			if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] resolved {:?} to {:?}", name.value, found_defs); }
			Ok(found_defs)
		}
	}

	/// Resolve a compound name within a scope.
	pub fn resolve_compound_name<'a>(&self, name: &'a ast::CompoundName, scope_id: ScopeRef, only_defs: bool) -> Result<(ResolvableName, Vec<Spanned<Def>>, Span, &'a [ast::NamePart])> {
		if self.sess.opts.trace_scoreboard { println!("[SB][VHDL] resolve compound {:?} in scope {:?}", name, scope_id); }

		// First resolve the primary name.
		let mut seen_span = name.primary.span;
		let mut res_name = self.resolvable_from_primary_name(&name.primary)?;
		let mut defs = self.resolve_name(res_name, scope_id, only_defs, false)?;

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
						self.emit(d);
						return Err(());
					};

					// Make sure that we can map the definition to a scope
					// reference. We can only select into things that have a
					// scope of their own.
					let scope = match def.value {
						Def::Lib(id) => id.into(),
						Def::Pkg(id) => id.into(),
						// Def::PkgInst(id) => id.into(),
						Def::BuiltinPkg(id) => id.into(),
						d => {
							self.emit(
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
					defs = self.resolve_name(res_name, scope, true, false)?;
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

	/// Get the builtin type `standard.boolean`.
	pub fn builtin_boolean_type(&self) -> &'ctx Ty {
		self.intern_ty(Ty::Null)
	}

	/// Get the builtin type `standard.time`.
	pub fn builtin_time_type(&self) -> &'ctx Ty {
		self.intern_ty(Ty::Null)
	}

	/// Get the builtin type `standard.string`.
	pub fn builtin_string_type(&self) -> &'ctx Ty {
		self.intern_ty(Ty::Null)
	}

	/// Get the builtin type `standard.severity`.
	pub fn builtin_severity_type(&self) -> &'ctx Ty {
		self.intern_ty(Ty::Null)
	}
}

// Group the architectures declared in a library by entity.
impl<'lazy, 'sb, 'ast, 'ctx> NodeMaker<LibRef, &'ctx ArchTable> for ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
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
					self.emit(
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
							self.emit(
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
					self.emit(
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
impl<'lazy, 'sb, 'ast, 'ctx> NodeMaker<ArchRef, DeclValueRef> for ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
	fn make(&self, _: ArchRef) -> Result<DeclValueRef> {
		unimplemented!();
	}
}


// Generate the definition for an architecture.
impl<'lazy, 'sb, 'ast, 'ctx> NodeMaker<ArchRef, DefValueRef> for ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
	fn make(&self, id: ArchRef) -> Result<DefValueRef> {
		// Type check the entire library where the architecture is defined in.
		let typeck_ctx = TypeckContext::new(self);
		typeck_ctx.typeck(self.ast(id).0); // typeck the entire library
		if !typeck_ctx.finish() {
			return Err(());
		}
		// self.typeck(id)?;
		// self.typeck(self.ast(id).0)?; // typeck the entire library

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

		// Generate the code for the statements in the architecture.
		for &stmt_id in &hir.stmts {
			self.codegen(stmt_id, &mut entity)?;
		}

		// Add the entity to the module and return a reference to it.
		Ok(DefValueRef(self.sb.llmod.borrow_mut().add_entity(entity).into()))
	}
}


impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
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
			Ty::Access(_) => Ok(self.intern_const(Const::Null)),
			Ty::Array(ref ty) => {
				self.emit(DiagBuilder2::bug(format!("default value for type `{}` not implemented", ty)));
				// TODO: Use the correct default value.
				Ok(self.intern_const(Const::Null))
			}
			Ty::File(ref ty) => {
				self.emit(DiagBuilder2::bug(format!("default value for type `{}` not implemented", ty)));
				// TODO: Use the correct default value.
				Ok(self.intern_const(Const::Null))
			}
			Ty::Record(ref ty) => {
				self.emit(DiagBuilder2::bug(format!("default value for type `{}` not implemented", ty)));
				// TODO: Use the correct default value.
				Ok(self.intern_const(Const::Null))
			}
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

impl ResolvableName {
	/// Check whether this name is an identifier.
	pub fn is_ident(&self) -> bool {
		match *self {
			ResolvableName::Ident(_) => true,
			_ => false,
		}
	}

	/// Check whether this name is a bit.
	pub fn is_bit(&self) -> bool {
		match *self {
			ResolvableName::Bit(_) => true,
			_ => false,
		}
	}

	/// Check whether this name is an operator.
	pub fn is_operator(&self) -> bool {
		match *self {
			ResolvableName::Operator(_) => true,
			_ => false,
		}
	}
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

impl<'ctx> From<&'ctx Ty> for TypeCtx<'ctx> {
	fn from(ty: &'ctx Ty) -> TypeCtx<'ctx> {
		TypeCtx::Type(ty)
	}
}

impl<'ctx, T> From<T> for TypeCtx<'ctx> where TypedNodeRef: From<T> {
	fn from(id: T) -> TypeCtx<'ctx> {
		TypeCtx::TypeOf(id.into())
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
node_ref!(AggregateRef);
node_ref!(IntfConstRef);
node_ref!(IntfSignalRef);
node_ref!(IntfVarRef);
node_ref!(IntfFileRef);
node_ref!(IntfPkgRef);
node_ref!(IntfSubprogRef);
node_ref!(IntfTypeRef);
node_ref!(LibRef);
node_ref!(PkgBodyRef);
node_ref!(PkgDeclRef);
node_ref!(PkgInstRef);
node_ref!(SubprogBodyRef);
node_ref!(SubprogDeclRef);
node_ref!(SubprogInstRef);
node_ref!(SubtypeIndRef);
node_ref!(TypeDeclRef);
node_ref!(SubtypeDeclRef);
node_ref!(WaitStmtRef);
node_ref!(AssertStmtRef);
node_ref!(ReportStmtRef);
node_ref!(SigAssignStmtRef);
node_ref!(VarAssignStmtRef);
node_ref!(CallStmtRef);
node_ref!(IfStmtRef);
node_ref!(CaseStmtRef);
node_ref!(LoopStmtRef);
node_ref!(NexitStmtRef);
node_ref!(ReturnStmtRef);
node_ref!(NullStmtRef);
node_ref!(BlockStmtRef);
node_ref!(ProcessStmtRef);
node_ref!(ConcCallStmtRef);
node_ref!(ConcAssertStmtRef);
node_ref!(ConcSigAssignStmtRef);
node_ref!(CompInstStmtRef);
node_ref!(ForGenStmtRef);
node_ref!(IfGenStmtRef);
node_ref!(CaseGenStmtRef);
node_ref!(ConstDeclRef);
node_ref!(SignalDeclRef);
node_ref!(VarDeclRef);
node_ref!(FileDeclRef);
node_ref!(AliasDeclRef);
node_ref!(CompDeclRef);
node_ref!(AttrDeclRef);
node_ref!(AttrSpecRef);
node_ref!(CfgSpecRef);
node_ref!(DisconSpecRef);
node_ref!(GroupDeclRef);
node_ref!(GroupTempRef);
node_ref!(ArrayTypeIndexRef);
node_ref!(GenericMapRef);
node_ref!(PortMapRef);
node_ref!(LatentTypeMarkRef);
node_ref!(LatentPkgRef);
node_ref!(LatentSubprogRef);

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
	Const(ConstDeclRef),
	Signal(SignalRef),
	File(FileDeclRef),
	Var(VarDeclRef),
	Alias(AliasDeclRef),
	Comp(CompDeclRef),
	Attr(AttrDeclRef),
	GroupTemp(GroupTempRef),
	Group(GroupDeclRef),
	Subprog(SubprogDeclRef),
	SubprogInst(SubprogInstRef),
	Stmt(StmtRef),
);

node_ref_group!(ScopeRef:
	Lib(LibRef),
	CtxItems(CtxItemsRef),
	Entity(EntityRef),
	BuiltinPkg(BuiltinPkgRef),
	Pkg(PkgDeclRef),
	PkgBody(PkgBodyRef),
	Arch(ArchRef),
	Process(ProcessStmtRef),
	Subprog(SubprogDeclRef),
	SubprogBody(SubprogBodyRef),
);

node_ref_group!(GenericRef:
	Type(IntfTypeRef),
	Subprog(IntfSubprogRef),
	Pkg(IntfPkgRef),
	Const(IntfConstRef),
);

/// An interface object.
node_ref_group!(IntfObjRef:
	Const(IntfConstRef),
	Var(IntfVarRef),
	Signal(IntfSignalRef),
	File(IntfFileRef),
);

node_ref_group!(TypeMarkRef:
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
);

impl From<TypeMarkRef> for Def {
	fn from(tm: TypeMarkRef) -> Def {
		match tm {
			TypeMarkRef::Type(id) => id.into(),
			TypeMarkRef::Subtype(id) => id.into(),
		}
	}
}

node_ref_group!(SignalRef:
	Intf(IntfSignalRef),
	Decl(SignalDeclRef),
);

node_ref_group!(PkgRef:
	Decl(PkgDeclRef),
	Inst(PkgInstRef),
);

node_ref_group!(SubprogRef:
	Decl(SubprogDeclRef),
	Inst(SubprogInstRef),
);

/// All declarations that may possibly appear in a package. See IEEE 1076-2008
/// section 4.7.
///
/// ```text
/// [x] subprogram_declaration
/// [x] subprogram_instantiation_declaration
/// [x] package_declaration
/// [x] package_instantiation_declaration
/// [x] type_declaration
/// [x] subtype_declaration
/// [x] constant_declaration
/// [x] signal_declaration
/// [x] variable_declaration
/// [x] file_declaration
/// [x] alias_declaration
/// [x] component_declaration
/// [x] attribute_declaration
/// [x] attribute_specification
/// [x] disconnection_specification
/// [ ] use_clause
/// [x] group_template_declaration
/// [x] group_declaration
/// ```
node_ref_group!(DeclInPkgRef:
	Subprog(SubprogDeclRef),
	SubprogInst(SubprogInstRef),
	Pkg(PkgDeclRef),
	PkgInst(PkgInstRef),
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
	Const(ConstDeclRef),
	Signal(SignalDeclRef),
	Var(VarDeclRef),
	File(FileDeclRef),
	Alias(AliasDeclRef),
	Comp(CompDeclRef),
	Attr(AttrDeclRef),
	AttrSpec(AttrSpecRef),
	Discon(DisconSpecRef),
	GroupTemp(GroupTempRef),
	Group(GroupDeclRef),
);

/// All declarations that may possibly appear in a package body. See IEEE
/// 1076-2008 section 4.8.
///
/// ```text
/// [x] subprogram_declaration
/// [x] subprogram_body
/// [x] subprogram_instantiation_declaration
/// [x] package_declaration
/// [x] package_body
/// [x] package_instantiation_declaration
/// [x] type_declaration
/// [x] subtype_declaration
/// [x] constant_declaration
/// [x] variable_declaration
/// [x] file_declaration
/// [x] alias_declaration
/// [x] attribute_declaration
/// [x] attribute_specification
/// [ ] use_clause
/// [x] group_template_declaration
/// [x] group_declaration
/// ```
node_ref_group!(DeclInPkgBodyRef:
	Subprog(SubprogDeclRef),
	SubprogBody(SubprogBodyRef),
	SubprogInst(SubprogInstRef),
	Pkg(PkgDeclRef),
	PkgBody(PkgBodyRef),
	PkgInst(PkgInstRef),
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
	Const(ConstDeclRef),
	Var(VarDeclRef),
	File(FileDeclRef),
	Alias(AliasDeclRef),
	Attr(AttrDeclRef),
	AttrSpec(AttrSpecRef),
	GroupTemp(GroupTempRef),
	Group(GroupDeclRef),
);

/// All declarations that may possibly appear in a subprogram. See IEEE
/// 1076-2008 section 4.3.
///
/// ```text
/// [x] subprogram_declaration
/// [x] subprogram_body
/// [x] subprogram_instantiation_declaration
/// [x] package_declaration
/// [x] package_body
/// [x] package_instantiation_declaration
/// [x] type_declaration
/// [x] subtype_declaration
/// [x] constant_declaration
/// [x] variable_declaration
/// [x] file_declaration
/// [x] alias_declaration
/// [x] attribute_declaration
/// [x] attribute_specification
/// [ ] use_clause
/// [x] group_template_declaration
/// [x] group_declaration
/// ```
node_ref_group!(DeclInSubprogRef:
	Subprog(SubprogDeclRef),
	SubprogBody(SubprogBodyRef),
	SubprogInst(SubprogInstRef),
	Pkg(PkgDeclRef),
	PkgBody(PkgBodyRef),
	PkgInst(PkgInstRef),
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
	Const(ConstDeclRef),
	Var(VarDeclRef),
	File(FileDeclRef),
	Alias(AliasDeclRef),
	Attr(AttrDeclRef),
	AttrSpec(AttrSpecRef),
	GroupTemp(GroupTempRef),
	Group(GroupDeclRef),
);

/// All declarations that may possibly appear in a block. See IEEE 1076-2008
/// section 3.3.2.
///
/// ```text
/// [x] subprogram_declaration
/// [x] subprogram_body
/// [x] subprogram_instantiation_declaration
/// [x] package_declaration
/// [x] package_body
/// [x] package_instantiation_declaration
/// [x] type_declaration
/// [x] subtype_declaration
/// [x] constant_declaration
/// [x] signal_declaration
/// [x] shared_variable_declaration
/// [x] file_declaration
/// [x] alias_declaration
/// [x] component_declaration
/// [x] attribute_declaration
/// [x] attribute_specification
/// [x] configuration_specification
/// [x] disconnection_specification
/// [ ] use_clause
/// [x] group_template_declaration
/// [x] group_declaration
/// ```
node_ref_group!(DeclInBlockRef:
	Subprog(SubprogDeclRef),
	SubprogBody(SubprogBodyRef),
	SubprogInst(SubprogInstRef),
	Pkg(PkgDeclRef),
	PkgBody(PkgBodyRef),
	PkgInst(PkgInstRef),
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
	Const(ConstDeclRef),
	Signal(SignalDeclRef),
	Var(VarDeclRef),
	File(FileDeclRef),
	Alias(AliasDeclRef),
	Comp(CompDeclRef),
	Attr(AttrDeclRef),
	AttrSpec(AttrSpecRef),
	CfgSpec(CfgSpecRef),
	Discon(DisconSpecRef),
	GroupTemp(GroupTempRef),
	Group(GroupDeclRef),
);

/// All declarations that may possibly appear in a process statement. See IEEE
/// 1076-2008 section 11.3.
///
/// ```text
/// [x] subprogram_declaration
/// [x] subprogram_body
/// [x] subprogram_instantiation_declaration
/// [x] package_declaration
/// [x] package_body
/// [x] package_instantiation_declaration
/// [x] type_declaration
/// [x] subtype_declaration
/// [x] constant_declaration
/// [x] variable_declaration
/// [x] file_declaration
/// [x] alias_declaration
/// [x] attribute_declaration
/// [x] attribute_specification
/// [ ] use_clause
/// [x] group_template_declaration
/// [x] group_declaration
/// ```
node_ref_group!(DeclInProcRef:
	Subprog(SubprogDeclRef),
	SubprogBody(SubprogBodyRef),
	SubprogInst(SubprogInstRef),
	Pkg(PkgDeclRef),
	PkgBody(PkgBodyRef),
	PkgInst(PkgInstRef),
	Type(TypeDeclRef),
	Subtype(SubtypeDeclRef),
	Const(ConstDeclRef),
	Var(VarDeclRef),
	File(FileDeclRef),
	Alias(AliasDeclRef),
	Attr(AttrDeclRef),
	AttrSpec(AttrSpecRef),
	GroupTemp(GroupTempRef),
	Group(GroupDeclRef),
);

/// All concurrent statements. See IEEE 1076-2008 section 11.
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
	ConcProcCall(ConcCallStmtRef),
	ConcAssert(ConcAssertStmtRef),
	ConcSigAssign(ConcSigAssignStmtRef),
	CompInst(CompInstStmtRef),
	ForGen(ForGenStmtRef),
	IfGen(IfGenStmtRef),
	CaseGen(CaseGenStmtRef),
);

/// All sequential statements. See IEEE 1076-2008 section 10.
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
	ProcCall(CallStmtRef),
	If(IfStmtRef),
	Case(CaseStmtRef),
	Loop(LoopStmtRef),
	Nexit(NexitStmtRef),
	Return(ReturnStmtRef),
	Null(NullStmtRef),
);

/// All statements. See IEEE 1076-2008 section 10 and 11.
node_ref_group!(StmtRef:
	Conc(ConcStmtRef),
	Seq(SeqStmtRef),
);

/// A reference to a node which has a type.
node_ref_group!(TypedNodeRef:
	SubtypeInd(SubtypeIndRef),
	Signal(SignalRef),
);


// Declare the node tables.
node_storage!(AstTable<'ast>:
	// subtys: SubtypeIndRef => (ScopeRef, &'ast ast::SubtypeInd),
	ctx_items: CtxItemsRef => (ScopeRef, &'ast [ast::CtxItem]),

	// The design units are tuples that also carry the list of context items
	// that were defined before them.
	entity_decls: EntityRef  => (LibRef, CtxItemsRef, &'ast ast::EntityDecl),
	cfg_decls:    CfgRef     => (LibRef, CtxItemsRef, &'ast ast::CfgDecl),
	pkg_decls:    PkgDeclRef => (ScopeRef, &'ast ast::PkgDecl),
	pkg_insts:    PkgInstRef => (ScopeRef, &'ast ast::PkgInst),
	ctx_decls:    CtxRef     => (LibRef, CtxItemsRef, &'ast ast::CtxDecl),
	arch_bodies:  ArchRef    => (LibRef, CtxItemsRef, &'ast ast::ArchBody),
	pkg_bodies:   PkgBodyRef => (ScopeRef, &'ast ast::PkgBody),

	// Interface declarations
	intf_sigs:       IntfSignalRef      => (ScopeRef, &'ast ast::IntfObjDecl, SubtypeIndRef, &'ast ast::Ident),
	intf_types:      IntfTypeRef        => (ScopeRef, &'ast ast::TypeDecl),
	intf_subprogs:   IntfSubprogRef     => (ScopeRef, &'ast ast::IntfSubprogDecl),
	intf_pkgs:       IntfPkgRef         => (ScopeRef, &'ast ast::PkgInst),
	intf_consts:     IntfConstRef       => (ScopeRef, &'ast ast::IntfObjDecl, SubtypeIndRef, &'ast ast::Ident),

	// Declarations
	type_decls:            TypeDeclRef           => (ScopeRef, &'ast ast::TypeDecl),
	subtype_decls:         SubtypeDeclRef        => (ScopeRef, &'ast ast::SubtypeDecl),
	// const_decls:           ConstDeclRef          => (ScopeRef, &'ast ast::ObjDecl),
	signal_decls:          SignalDeclRef         => (ScopeRef, &'ast ast::ObjDecl),
	// variable_decls:        VarDeclRef            => (ScopeRef, &'ast ast::ObjDecl),
	// file_decls:            FileDeclRef           => (ScopeRef, &'ast ast::ObjDecl),
	subprog_bodies:        SubprogBodyRef        => (ScopeRef, &'ast ast::Subprog),
	subprog_decls:         SubprogDeclRef        => (ScopeRef, &'ast ast::Subprog),
	subprog_insts:         SubprogInstRef        => (ScopeRef, &'ast ast::Subprog),
	alias_decls:           AliasDeclRef          => (ScopeRef, &'ast ast::AliasDecl),
	comp_decls:            CompDeclRef           => (ScopeRef, &'ast ast::CompDecl),
	attr_decls:            AttrDeclRef           => (ScopeRef, &'ast ast::AttrDecl),
	attr_specs:            AttrSpecRef           => (ScopeRef, &'ast ast::AttrDecl),
	cfg_specs:             CfgSpecRef            => (ScopeRef, &'ast ast::CfgSpec),
	discon_specs:          DisconSpecRef         => (ScopeRef, &'ast ast::DisconSpec),
	group_decls:           GroupDeclRef          => (ScopeRef, &'ast ast::GroupDecl),
	group_temps:           GroupTempRef          => (ScopeRef, &'ast ast::GroupDecl),

	exprs: ExprRef => (ScopeRef, &'ast ast::Expr),

	// Statements
	proc_stmts:       ProcessStmtRef   => (ScopeRef, &'ast ast::Stmt),
	sig_assign_stmts: SigAssignStmtRef => (ScopeRef, &'ast ast::Stmt),
	var_assign_stmts: VarAssignStmtRef => (ScopeRef, &'ast ast::Stmt),

	array_type_indices: ArrayTypeIndexRef => (ScopeRef, &'ast ast::Expr),
	type_marks:         LatentTypeMarkRef => (ScopeRef, LatentName<'ast>),
	pkg_names:          LatentPkgRef      => (ScopeRef, LatentName<'ast>),
	subprog_names:      LatentSubprogRef  => (ScopeRef, LatentName<'ast>),
);

node_storage!(HirTable<'ctx>:
	libs:                  LibRef                => &'ctx hir::Lib,
	entities:              EntityRef             => &'ctx hir::Entity,
	archs:                 ArchRef               => &'ctx hir::Arch,
	intf_sigs:             IntfSignalRef         => &'ctx hir::IntfSignal,
	subtype_inds:          SubtypeIndRef         => &'ctx hir::SubtypeInd,
	pkgs:                  PkgDeclRef            => &'ctx hir::Package,
	pkg_bodies:            PkgBodyRef            => &'ctx hir::PackageBody,
	pkg_insts:             PkgInstRef            => &'ctx hir::PackageInst,
	type_decls:            TypeDeclRef           => &'ctx hir::TypeDecl,
	subtype_decls:         SubtypeDeclRef        => &'ctx hir::SubtypeDecl,
	exprs:                 ExprRef               => &'ctx hir::Expr,
	aggregate:             AggregateRef          => &'ctx hir::Aggregate,

	// Declarations
	const_decls:           ConstDeclRef          => &'ctx hir::Decl<hir::ConstDecl>,
	signal_decls:          SignalDeclRef         => &'ctx hir::SignalDecl,
	variable_decls:        VarDeclRef            => &'ctx hir::Decl<hir::VarDecl>,
	file_decls:            FileDeclRef           => &'ctx hir::Decl<hir::FileDecl>,
	process_stmts:         ProcessStmtRef        => &'ctx hir::ProcessStmt,
	sig_assign_stmts:      SigAssignStmtRef      => &'ctx hir::SigAssignStmt,
	array_type_indices:    ArrayTypeIndexRef     => &'ctx Spanned<hir::ArrayTypeIndex>,
	subprogs:              SubprogDeclRef        => &'ctx hir::Subprog,
	subprog_bodies:        SubprogBodyRef        => &'ctx hir::SubprogBody,
	subprog_insts:         SubprogInstRef        => &'ctx hir::SubprogInst,
	latent_type_marks:     LatentTypeMarkRef     => Spanned<TypeMarkRef>,
	latent_pkgs:           LatentPkgRef          => Spanned<PkgRef>,
	latent_subprogs:       LatentSubprogRef      => Spanned<SubprogRef>,
	// Sequential statements
	wait_stmts:            WaitStmtRef           => &'ctx hir::Stmt<hir::WaitStmt>,
	assert_stmts:          AssertStmtRef         => &'ctx hir::Stmt<hir::AssertStmt>,
	report_stmts:          ReportStmtRef         => &'ctx hir::Stmt<hir::ReportStmt>,
	// sig_assign_stmts:      SigAssignStmtRef      => &'ctx hir::Stmt<hir::SigAssignStmt>,
	var_assign_stmts:      VarAssignStmtRef      => &'ctx hir::Stmt<hir::VarAssignStmt>,
	call_stmt:             CallStmtRef           => &'ctx hir::Stmt<hir::CallStmt>,
	if_stmt:               IfStmtRef             => &'ctx hir::Stmt<hir::IfStmt>,
	case_stmt:             CaseStmtRef           => &'ctx hir::Stmt<hir::CaseStmt>,
	loop_stmt:             LoopStmtRef           => &'ctx hir::Stmt<hir::LoopStmt>,
	nexit_stmt:            NexitStmtRef          => &'ctx hir::Stmt<hir::NexitStmt>,
	return_stmt:           ReturnStmtRef         => &'ctx hir::Stmt<hir::ReturnStmt>,
	null_stmt:             NullStmtRef           => &'ctx hir::Stmt<hir::NullStmt>,
);

// node_storage!(LazyHirTable<'ast, 'ctx>:
// 	wait_stmts: WaitStmtRef => LazyNode<'ctx, hir::Stmt<hir::WaitStmt>, &'ast ()>,
// );


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


/// A general name in the AST that can be resolved. Used for e.g. for package
/// and subprogram bodies to resolve the name of their target.
#[derive(Copy, Clone, Debug)]
pub enum LatentName<'ast> {
	/// A simple name.
	Simple(&'ast Spanned<Name>),
	/// A primary name.
	Primary(&'ast ast::PrimaryName),
	/// A compound name.
	Compound(&'ast ast::CompoundName),
}

impl<'ast> From<&'ast Spanned<Name>> for LatentName<'ast> {
	fn from(other: &'ast Spanned<Name>) -> LatentName<'ast> {
		LatentName::Simple(other)
	}
}

impl<'ast> From<&'ast ast::PrimaryName> for LatentName<'ast> {
	fn from(other: &'ast ast::PrimaryName) -> LatentName<'ast> {
		LatentName::Primary(other)
	}
}

impl<'ast> From<&'ast ast::CompoundName> for LatentName<'ast> {
	fn from(other: &'ast ast::CompoundName) -> LatentName<'ast> {
		LatentName::Compound(other)
	}
}

impl<'ast> HasSpan for LatentName<'ast> {
	fn span(&self) -> Span {
		match *self {
			LatentName::Simple(n)   => n.span,
			LatentName::Primary(n)  => n.span,
			LatentName::Compound(n) => n.span,
		}
	}
}

impl<'ast> HasDesc for LatentName<'ast> {
	fn desc(&self) -> &'static str {
		"name"
	}
}
