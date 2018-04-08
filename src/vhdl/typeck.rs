// Copyright (c) 2017 Fabian Schuiki

//! This module implements the type calculation of the scoreboard.

use std::fmt::Debug;
use std::cell::Cell;
use std::collections::HashMap;

use common::{NodeId, Verbosity};
use common::errors::*;
use common::source::{Span, Spanned, INVALID_SPAN};
use common::score::{NodeMaker, NodeStorage, Result};
use score::*;
use ty::*;
use konst::*;
use hir;
use lazy::LazyNode;

/// A context to typecheck things in.
///
/// This context helps checking the types of things and keeping track of errors.
pub struct TypeckContext<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb> {
	/// The parent context.
	pub ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>,
	/// Whether any of the type checking failed.
	failed: Cell<bool>,
}

impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
	/// Create a new type checking context.
	pub fn new(ctx: &'sbc ScoreContext<'lazy, 'sb, 'ast, 'ctx>) -> TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
		TypeckContext {
			ctx: ctx,
			failed: Cell::new(false),
		}
	}

	/// Consume the context and return the result of the typeck.
	pub fn finish(self) -> bool {
		!self.failed.get()
	}

	/// Emit a diagnostic message.
	pub fn emit(&self, diag: DiagBuilder2) {
		if diag.severity >= Severity::Error {
			self.failed.set(true);
		}
		self.ctx.sess.emit(diag)
	}

	/// Check the type of a node.
	///
	/// If the node already had its type checked, immediately returns the result
	/// of that operation. Otherwise runs the task scheduled in the lazy table.
	pub fn lazy_typeck<I>(&self, id: I) where I: Into<NodeId> {
		let id = id.into();

		// If the typeck has already been performed, return its result.
		if let Some(&node) = self.ctx.sb.typeck_table.borrow().get(&id) {
			if node.is_err() {
				self.failed.set(true);
			}
			return;
		}

		// Otherwise run the task scheduled in the lazy typeck table, then store
		// the result.
		let task = self.ctx.lazy.typeck.borrow_mut().set(id, LazyNode::Running);
		let result = match task {
			Some(LazyNode::Pending(f)) => f(self),
			Some(LazyNode::Running) => { self.ctx.bug(id, format!("recursion on typeck of {:?}", id)); Err(()) }
			None => { self.ctx.bug(id, format!("no typeck scheduled for {:?}", id)); Err(()) }
		};
		if result.is_err() {
			self.failed.set(true);
		}
		self.ctx.sb.typeck_table.borrow_mut().insert(id, result);
	}

	/// Determine the type of a node.
	///
	/// If the node already had its type determined, immediately returns the
	/// result of that operation. Otherwise runs the task scheduled in the lazy
	/// table.
	pub fn lazy_typeval<I>(&self, id: I) -> Result<&'ctx Ty> where I: Into<NodeId> {
		let id = id.into();

		// If the typeval has already been performed, return its result.
		if let Some(&node) = self.ctx.sb.typeval_table.borrow().get(&id) {
			return node;
		}

		// Otherwise run the task scheduled in the lazy typeval table, then store
		// the result.
		let task = self.ctx.lazy.typeval.borrow_mut().set(id, LazyNode::Running);
		let result = match task {
			Some(LazyNode::Pending(f)) => f(self),
			Some(LazyNode::Running) => { self.ctx.bug(id, format!("recursion on typeval of {:?}", id)); Err(()) }
			None => { self.ctx.bug(id, format!("no typeval scheduled for {:?}", id)); Err(()) }
		};
		if result.is_err() {
			self.failed.set(true);
		}

		// Emit a diagnostic for the determined type if the corresponding flag
		// is active.
		if self.ctx.sess.opts.verbosity.contains(Verbosity::TYPES) {
			match (result, self.ctx.span(id)) {
				(Ok(ty), Some(span)) => {
					self.emit(
						DiagBuilder2::note(format!("type of `{}` is {}", span.extract(), ty))
						.span(span)
					);
				}
				_ => ()
			}
		}

		self.ctx.sb.typeval_table.borrow_mut().insert(id, result);
		result
	}

	/// Ensure that two types are compatible.
	pub fn must_match(&self, exp: &'ctx Ty, act: &'ctx Ty, span: Span) -> bool {
		assert!(span != INVALID_SPAN);
		if self.ctx.sess.opts.verbosity.contains(Verbosity::TYPECK) {
			self.emit(
				DiagBuilder2::note(format!("typeck expected {} and actual {}", exp, act))
				.span(span)
			);
		}
		if exp == act {
			return true;
		}
		let (exp_flat, act_flat) = match (self.ctx.deref_named_type(exp), self.ctx.deref_named_type(act)) {
			(Ok(e), Ok(a)) => (e, a),
			_ => return false,
		};
		match (exp_flat, act_flat) {
			(e,a) if e == a => return true,
			// (e,a) if a.is_subtype_of(e) => return true,
			(&Ty::Int(..), &Ty::UniversalInt) => return true,
			_ => ()
		}
		self.emit(
			DiagBuilder2::error(format!("expected type {}, but `{}` has type {}", exp, span.extract(), act))
			.span(span)
			.add_note(format!("expected type: {}", exp_flat))
			.add_note(format!("  actual type: {}", act_flat))
		);
		false
	}

	/// Ensure that one type can be cast into the other.
	pub fn must_cast(&self, into: &'ctx Ty, from: &'ctx Ty, span: Span) -> bool {
		self.must_match(into, from, span)
	}

	/// Type check the time expression in a delay mechanism.
	pub fn typeck_delay_mechanism(&self, _node: &'ctx hir::DelayMechanism) {
		// TODO: implement this
	}

	/// Type check a waveform.
	pub fn typeck_waveform(&self, node: &'ctx hir::Waveform, exp: &'ctx Ty) {
		for elem in node {
			self.typeck_wave_elem(elem, exp);
		}
	}

	/// Type check a waveform element.
	pub fn typeck_wave_elem(&self, node: &'ctx hir::WaveElem, exp: &'ctx Ty) {
		if let Some(value) = node.value {
			self.typeck_node(value, exp);
		}
		if let Some(_after) = node.after {
			// TODO: type check time expression
			// self.typeck_node(after, /* time type */);
		}
	}

	/// Type check a subprogram specification.
	pub fn typeck_subprog_spec(&self, node: &'ctx hir::SubprogSpec) {
		self.typeck_slice(&node.generics);
		// self.typeck_slice(&node.generic_map);
		self.typeck_slice(&node.params);
		if let Some(ref ty) = node.return_type {
			self.typeck(ty.value);
		}
	}

	/// Type check any node that can have its type calculated.
	pub fn typeck_node<I>(&self, id: I, exp: &'ctx Ty)
		where
			I: 'ctx + Copy + Debug + Into<NodeId>,
			ScoreContext<'lazy, 'sb, 'ast, 'ctx>: NodeMaker<I, &'ctx Ty>
	{
		if let Ok(act) = self.ctx.ty(id) {
			if act != exp {
				// TODO: We need some span information here!
				self.emit(
					DiagBuilder2::error(format!("typecheck failed, expected {:?}, got {:?}", exp, act))
				);
			}
		} else {
			self.failed.set(true);
		}
	}

	/// Type check a slice of nodes.
	pub fn typeck_slice<T,I>(&self, ids: T)
		where
			T: AsRef<[I]>,
			I: Copy,
			TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx>: Typeck<I>,
	{
		for &id in ids.as_ref() {
			self.typeck(id);
		}
	}

	/// Apply a range constraint to a type.
	pub fn apply_range_constraint(&self, ty: &Ty, con: Spanned<&hir::Range>) -> Result<&'ctx Ty> {
		// Determine the applied range.
		let (dir, lb, rb) = match *con.value {
			hir::Range::Immediate(dir, lb, rb) => (dir, lb, rb),
		};
		let lb = self.ctx.const_value(lb)?;
		let rb = self.ctx.const_value(rb)?;

		// Determine the inner type to which the constraint shall be applied.
		let ty = self.ctx.deref_named_type(ty)?;
		match *ty {
			Ty::Int(ref ty) => {
				// Make sure we have an integer range.
				let (lb, rb) = match (lb, rb) {
					(&Const::Int(ref lb), &Const::Int(ref rb)) => (lb, rb),
					_ => {
						self.emit(
							DiagBuilder2::error(format!("non-integer range `{} {} {}` cannot constrain an integer type", lb, dir, rb))
							.span(con.span)
						);
						return Err(());
					}
				};

				// Make sure that this is actually a subtype.
				if ty.dir != dir || ty.left_bound > lb.value || ty.right_bound < rb.value {
					self.emit(
						DiagBuilder2::error(format!("`{} {} {}` is not a subrange of `{}`", lb, dir, rb, ty))
						.span(con.span)
					);
					return Err(());
				}

				// Create the new type.
				Ok(self.ctx.intern_ty(IntTy::new(ty.dir, lb.value.clone(), rb.value.clone()).maybe_null()))
			}

			// All other types we simply cannot constrain by range.
			_ => {
				self.emit(
					DiagBuilder2::error(format!("{} cannot be constrained by range", ty.kind_desc()))
					.span(con.span)
				);
				return Err(());
			}
		}
	}

	/// Apply an array constraint to a type.
	pub fn apply_array_constraint(&self, ty: &'ctx Ty, con: Spanned<&hir::ArrayConstraint>) -> Result<&'ctx Ty> {
		// Determine the inner type to which the constraint shall be applied.
		let ty = self.ctx.deref_named_type(ty)?;
		match *ty {
			Ty::Array(ref ty) => {
				let indices = if !con.value.index.is_empty() {
					if con.value.index.len() != ty.indices.len() {
						self.emit(
							DiagBuilder2::error(format!("constrained {} indices, but array has {}", con.value.index.len(), ty.indices.len()))
							.span(con.span)
							.add_note(format!("`{}` constrained with `{}`", ty, con.span.extract()))
						);
						return Err(());
					}
					ty.indices.iter()
						.zip(con.value.index.iter())
						.map(|(ty, con)| self.apply_index_constraint(ty, con.as_ref()))
						.collect::<Result<Vec<_>>>()?
				} else {
					ty.indices.clone()
				};
				let element = if let Some(ref elem_con) = con.value.elem {
					match elem_con.value {
						hir::ElementConstraint::Array(ref ac) => {
							self.apply_array_constraint(&*ty.element, Spanned::new(ac, elem_con.span))?
						}
						hir::ElementConstraint::Record(ref rc) => {
							self.apply_record_constraint(&*ty.element, Spanned::new(rc, elem_con.span))?
						}
					}
				} else {
					&*ty.element
				};
				Ok(self.ctx.intern_ty(ArrayTy::new(indices, Box::new(element.clone()))))
			}
			_ => {
				self.emit(
					DiagBuilder2::error(format!("array constraint `{}` does not apply to {}", con.span.extract(), ty.kind_desc()))
					.span(con.span)
				);
				return Err(());
			}
		}
	}

	/// Apply a record constraint to a type.
	pub fn apply_record_constraint(&self, ty: &'ctx Ty, con: Spanned<&hir::RecordConstraint>) -> Result<&'ctx Ty> {
		use moore_common::name::Name;
		// Determine the inner type to which the constraint shall be applied.
		let ty = self.ctx.deref_named_type(ty)?;
		match *ty {
			Ty::Record(ref ty) => {
				let mut fields: Vec<(Name, &Ty)> = ty.fields
					.iter()
					.map(|&(name, ref ty)| (name, ty.as_ref()))
					.collect();
				let mut had_fails = false;
				for &(name, ref con) in &con.value.elems {
					// Find the field that we're supposed to constrain.
					let idx = match ty.lookup.get(&name.value) {
						Some(&idx) => idx,
						None => {
							self.emit(
								DiagBuilder2::error(format!("record has no element `{}`", name.value))
								.span(name.span)
								.add_note(format!("{}", ty))
							);
							had_fails = true;
							continue;
						}
					};

					// Constrain the field.
					fields[idx].1 = match con.value {
						hir::ElementConstraint::Array(ref ac) => {
							self.apply_array_constraint(&fields[idx].1, Spanned::new(ac, con.span))?
						}
						hir::ElementConstraint::Record(ref rc) => {
							self.apply_record_constraint(&fields[idx].1, Spanned::new(rc, con.span))?
						}
					};
				}
				if had_fails {
					return Err(());
				}
				let fields = fields.into_iter().map(|(name, ty)| (name, Box::new(ty.clone()))).collect();
				Ok(self.ctx.intern_ty(RecordTy::new(fields)))
			}
			_ => {
				self.emit(
					DiagBuilder2::error(format!("array constraint `{}` does not apply to {}", con.span.extract(), ty.kind_desc()))
					.span(con.span)
				);
				return Err(());
			}
		}
	}

	/// Apply an index constraint to an array index.
	pub fn apply_index_constraint(&self, index: &'ctx ArrayIndex, con: Spanned<&hir::DiscreteRange>) -> Result<ArrayIndex> {
		// Convert the discrete range applied as constraint into a type.
		let con_ty = Spanned::new(self.ctx.deref_named_type(self.type_from_discrete_range(con)?)?, con.span);

		// Impose the type as a subtype on the index.
		let index_ty = match *index {
			ArrayIndex::Unbounded(ref ty) | ArrayIndex::Constrained(ref ty) => {
				self.apply_subtype(&*ty, con_ty)?
			}
		};

		Ok(ArrayIndex::Constrained(Box::new(index_ty.clone())))
	}

	/// Impose a subtype on a type.
	pub fn apply_subtype(&self, orig_ty: &'ctx Ty, subty: Spanned<&Ty>) -> Result<&'ctx Ty> {
		let deref = self.ctx.deref_named_type(orig_ty)?;
		let span = subty.span;
		match (deref, self.ctx.deref_named_type(subty.value)?) {
			(&Ty::Int(ref ty), &Ty::Int(ref subty)) => {
				use std::cmp::{max, min};
				if ty.dir != subty.dir {
					self.emit(
						DiagBuilder2::error(format!("directions disagree; `{}` and `{}`", subty, ty))
						.span(span)
					);
					return Err(());
				}
				let (ty_lo, ty_hi, subty_lo, subty_hi) = match ty.dir {
					Dir::To => (&ty.left_bound, &ty.right_bound, &subty.left_bound, &subty.right_bound),
					Dir::Downto => (&ty.right_bound, &ty.left_bound, &subty.right_bound, &subty.left_bound),
				};
				if ty_lo > subty_lo || ty_hi < subty_hi {
					self.emit(
						DiagBuilder2::error(format!("`{}` is not a subrange of `{}`", subty, ty))
						.span(span)
						.add_note("The range of a subtype must be entirely contained within the range of the target type.")
						// TODO: Add reference to standard.
					);
				}
				let lo = max(ty_lo, subty_lo);
				let hi = min(ty_hi, subty_hi);
				let (lb, rb) = match ty.dir {
					Dir::To => (lo, hi),
					Dir::Downto => (hi, lo),
				};
				let new_ty: Ty = IntTy::new(ty.dir, lb.clone(), rb.clone()).into();
				if &new_ty == deref {
					Ok(orig_ty)
				} else {
					Ok(self.ctx.intern_ty(new_ty))
				}
			}
			_ => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is not a subtype of `{}`", subty.span.extract(), orig_ty))
					.span(span)
				);
				return Err(());
			}
		}
	}

	/// Evaluate a discrete range as a type.
	pub fn type_from_discrete_range(&self, range: Spanned<&hir::DiscreteRange>) -> Result<&'ctx Ty> {
		match *range.value {
			hir::DiscreteRange::Subtype(id) => self.ctx.ty(id),
			hir::DiscreteRange::Range(ref r) => self.type_from_range(Spanned::new(r, range.span)),
		}
	}

	/// Evaluate a range as a type.
	pub fn type_from_range(&self, range: Spanned<&hir::Range>) -> Result<&'ctx Ty> {
		match *range.value {
			hir::Range::Immediate(dir, lb, rb) => {
				let lb = self.ctx.const_value(lb)?;
				let rb = self.ctx.const_value(rb)?;
				match (lb, rb) {
					(&Const::Int(ref lb), &Const::Int(ref rb)) => {
						Ok(self.ctx.intern_ty(IntTy::new(dir, lb.value.clone(), rb.value.clone())))
					}
					_ => {
						self.emit(
							DiagBuilder2::error(format!("`{} {} {}` is not a valid range", lb, dir, rb))
							.span(range.span)
						);
						return Err(());
					}
				}
			}
		}
	}
}

use ty2::RangeDir;
impl From<Dir> for RangeDir {
	fn from(d: Dir) -> RangeDir {
		match d {
			Dir::To => RangeDir::To,
			Dir::Downto => RangeDir::Downto,
		}
	}
}

/// Performs a type check.
pub trait Typeck<I> {
	fn typeck(&self, id: I);
}

/// A macro to implement the `Typeck` trait.
macro_rules! impl_typeck {
	($slf:tt, $id:ident: $id_ty:ty => $blk:block) => {
		impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> Typeck<$id_ty> for TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
			fn typeck(&$slf, $id: $id_ty) $blk
		}
	}
}

/// A macro to implement the `Typeck` trait.
macro_rules! impl_typeck_err {
	($slf:tt, $id:ident: $id_ty:ty => $blk:block) => {
		impl<'sbc, 'lazy, 'sb, 'ast, 'ctx> Typeck<$id_ty> for TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> {
			fn typeck(&$slf, $id: $id_ty) {
				use std;
				let res = (move || -> Result<()> { $blk })();
				std::mem::forget(res);
			}
		}
	}
}

// Implement the `Typeck` trait for everything that supports type calculation.
impl<'sbc, 'lazy: 'sbc, 'sb: 'lazy, 'ast: 'sb, 'ctx: 'sb, I> Typeck<I> for TypeckContext<'sbc, 'lazy, 'sb, 'ast, 'ctx> where ScoreContext<'lazy, 'sb, 'ast, 'ctx>: NodeMaker<I, &'ctx Ty> {
	fn typeck(&self, id: I) {
		match ScoreContext::make(self.ctx, id) {
			Ok(_) => (),
			Err(()) => self.failed.set(true),
		}
	}
}

/// Checks whether a node is of a given type.
pub trait TypeckNode<'ctx, I> {
	fn typeck_node(&self, id: I, expected: &'ctx Ty) -> Result<()>;
}

// Implement the `TypeckNode` trait for everything that supports type
// calculation.
impl<'lazy, 'sb, 'ast, 'ctx, I> TypeckNode<'ctx, I> for ScoreContext<'lazy, 'sb, 'ast, 'ctx> where ScoreContext<'lazy, 'sb, 'ast, 'ctx>: NodeMaker<I, &'ctx Ty> {
	fn typeck_node(&self, id: I, expected: &'ctx Ty) -> Result<()> {
		let actual = self.make(id)?;
		if actual != expected {
			self.emit(
				DiagBuilder2::error(format!("typecheck failed, expected {:?}, got {:?}", expected, actual))
			);
			Err(())
		} else {
			Ok(())
		}
	}
}

macro_rules! unimp {
	($slf:tt, $id:expr) => {{
		$slf.emit(DiagBuilder2::bug(format!("typeck of {:?} not implemented", $id)));
		return;
	}}
}

macro_rules! unimp_err {
	($slf:tt, $id:expr) => {{
		$slf.emit(DiagBuilder2::bug(format!("typeck of {:?} not implemented", $id)));
		return Err(());
	}}
}

macro_rules! unimpmsg {
	($slf:tt, $span:expr, $msg:expr) => {{
		$slf.emit(DiagBuilder2::bug(format!("{} not implemented", $msg)).span($span));
		return Err(());
	}}
}

impl_typeck_err!(self, id: LibRef => {
	let hir = self.ctx.hir(id)?;
	self.typeck_slice(&hir.pkg_decls);
	self.typeck_slice(&hir.pkg_insts);
	self.typeck_slice(&hir.pkg_bodies);
	self.typeck_slice(&hir.ctxs);
	self.typeck_slice(&hir.entities);
	self.typeck_slice(&hir.archs);
	self.typeck_slice(&hir.cfgs);
	Ok(())
});

impl_typeck_err!(self, id: PkgDeclRef => {
	let hir = self.ctx.hir(id)?;
	self.typeck_slice(&hir.generics);
	self.typeck_slice(&hir.decls);
	Ok(())
});

impl_typeck_err!(self, id: PkgBodyRef => {
	let hir = self.ctx.hir(id)?;
	self.typeck_slice(&hir.decls);
	Ok(())
});

impl_typeck_err!(self, id: PkgInstRef => {
	let _hir = self.ctx.hir(id)?;
	// self.typeck_slice(&hir.generic_map);
	Ok(())
});

impl_typeck!(self, id: CtxRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: CfgRef => {
	unimp!(self, id)
});

impl_typeck_err!(self, id: EntityRef => {
	let hir = self.ctx.hir(id)?;
	for &generic in &hir.generics {
		self.typeck(generic);
	}
	for &port in &hir.ports {
		self.typeck(port);
	}
	Ok(())
});

impl_typeck_err!(self, id: ArchRef => {
	let hir = self.ctx.hir(id)?;
	self.typeck(hir.entity);
	for &decl in &hir.decls {
		self.typeck(decl);
	}
	for &stmt in &hir.stmts {
		self.typeck(stmt);
	}
	Ok(())
});

impl_typeck!(self, id: GenericRef => {
	match id {
		GenericRef::Type(id)    => self.typeck(id),
		GenericRef::Subprog(id) => self.typeck(id),
		GenericRef::Pkg(id)     => self.typeck(id),
		GenericRef::Const(id)   => self.typeck(id),
	}
});

// impl_typeck!(self, id: IntfSignalRef => {
// 	self.typeck(self.hir(id)?.ty)
// });

impl_typeck!(self, id: IntfTypeRef => {
	unimp!(self, id)
	// self.typeck(self.hir(id)?.ty)
});

impl_typeck!(self, id: IntfSubprogRef => {
	unimp!(self, id)
	// self.typeck(self.hir(id)?.ty)
});

impl_typeck!(self, id: IntfPkgRef => {
	unimp!(self, id)
	// self.typeck(self.hir(id)?.ty)
});

impl_make!(self, id: IntfConstRef => &Ty {
	// TODO: Implement this.
	unimp_err!(self, id)
});

impl_make!(self, id: IntfVarRef => &Ty {
	// TODO: Implement this.
	unimp_err!(self, id)
});

impl_make!(self, id: IntfSignalRef => &Ty {
	let hir = self.hir(id)?;
	self.ty(hir.ty)
});

impl_make!(self, id: IntfFileRef => &Ty {
	// TODO: Implement this.
	unimp_err!(self, id)
});

impl_typeck!(self, id: DeclInPkgRef => {
	match id {
		DeclInPkgRef::Subprog(id)     => self.typeck(id),
		DeclInPkgRef::SubprogInst(id) => self.typeck(id),
		DeclInPkgRef::Pkg(id)         => self.typeck(id),
		DeclInPkgRef::PkgInst(id)     => self.typeck(id),
		DeclInPkgRef::Type(id)        => self.typeck(id),
		DeclInPkgRef::Subtype(id)     => self.typeck(id),
		DeclInPkgRef::Const(id)       => self.typeck(id),
		DeclInPkgRef::Signal(id)      => self.typeck(id),
		DeclInPkgRef::Var(id)         => self.typeck(id),
		DeclInPkgRef::File(id)        => self.typeck(id),
		DeclInPkgRef::Alias(id)       => self.typeck(id),
		DeclInPkgRef::Comp(id)        => self.typeck(id),
		DeclInPkgRef::Attr(id)        => self.typeck(id),
		DeclInPkgRef::AttrSpec(id)    => self.typeck(id),
		DeclInPkgRef::Discon(id)      => self.typeck(id),
		DeclInPkgRef::GroupTemp(id)   => self.typeck(id),
		DeclInPkgRef::Group(id)       => self.typeck(id),
	}
});

impl_typeck!(self, id: DeclInPkgBodyRef => {
	match id {
		DeclInPkgBodyRef::Subprog(id)     => self.typeck(id),
		DeclInPkgBodyRef::SubprogBody(id) => self.typeck(id),
		DeclInPkgBodyRef::SubprogInst(id) => self.typeck(id),
		DeclInPkgBodyRef::Pkg(id)         => self.typeck(id),
		DeclInPkgBodyRef::PkgBody(id)     => self.typeck(id),
		DeclInPkgBodyRef::PkgInst(id)     => self.typeck(id),
		DeclInPkgBodyRef::Type(id)        => self.typeck(id),
		DeclInPkgBodyRef::Subtype(id)     => self.typeck(id),
		DeclInPkgBodyRef::Const(id)       => self.typeck(id),
		DeclInPkgBodyRef::Var(id)         => self.typeck(id),
		DeclInPkgBodyRef::File(id)        => self.typeck(id),
		DeclInPkgBodyRef::Alias(id)       => self.typeck(id),
		DeclInPkgBodyRef::Attr(id)        => self.typeck(id),
		DeclInPkgBodyRef::AttrSpec(id)    => self.typeck(id),
		DeclInPkgBodyRef::GroupTemp(id)   => self.typeck(id),
		DeclInPkgBodyRef::Group(id)       => self.typeck(id),
	}
});

impl_typeck!(self, id: DeclInSubprogRef => {
	match id {
		DeclInSubprogRef::Subprog(id)     => self.typeck(id),
		DeclInSubprogRef::SubprogBody(id) => self.typeck(id),
		DeclInSubprogRef::SubprogInst(id) => self.typeck(id),
		DeclInSubprogRef::Pkg(id)         => self.typeck(id),
		DeclInSubprogRef::PkgBody(id)     => self.typeck(id),
		DeclInSubprogRef::PkgInst(id)     => self.typeck(id),
		DeclInSubprogRef::Type(id)        => self.typeck(id),
		DeclInSubprogRef::Subtype(id)     => self.typeck(id),
		DeclInSubprogRef::Const(id)       => self.typeck(id),
		DeclInSubprogRef::Var(id)         => self.typeck(id),
		DeclInSubprogRef::File(id)        => self.typeck(id),
		DeclInSubprogRef::Alias(id)       => self.typeck(id),
		DeclInSubprogRef::Attr(id)        => self.typeck(id),
		DeclInSubprogRef::AttrSpec(id)    => self.typeck(id),
		DeclInSubprogRef::GroupTemp(id)   => self.typeck(id),
		DeclInSubprogRef::Group(id)       => self.typeck(id),
	}
});

impl_typeck!(self, id: DeclInBlockRef => {
	match id {
		DeclInBlockRef::Subprog(id)     => self.typeck(id),
		DeclInBlockRef::SubprogBody(id) => self.typeck(id),
		DeclInBlockRef::SubprogInst(id) => self.typeck(id),
		DeclInBlockRef::Pkg(id)         => self.typeck(id),
		DeclInBlockRef::PkgBody(id)     => self.typeck(id),
		DeclInBlockRef::PkgInst(id)     => self.typeck(id),
		DeclInBlockRef::Type(id)        => self.typeck(id),
		DeclInBlockRef::Subtype(id)     => self.typeck(id),
		DeclInBlockRef::Const(id)       => self.typeck(id),
		DeclInBlockRef::Signal(id)      => self.typeck(id),
		DeclInBlockRef::Var(id)         => self.typeck(id),
		DeclInBlockRef::File(id)        => self.typeck(id),
		DeclInBlockRef::Alias(id)       => self.typeck(id),
		DeclInBlockRef::Comp(id)        => self.typeck(id),
		DeclInBlockRef::Attr(id)        => self.typeck(id),
		DeclInBlockRef::AttrSpec(id)    => self.typeck(id),
		DeclInBlockRef::CfgSpec(id)     => self.typeck(id),
		DeclInBlockRef::Discon(id)      => self.typeck(id),
		DeclInBlockRef::GroupTemp(id)   => self.typeck(id),
		DeclInBlockRef::Group(id)       => self.typeck(id),
	}
});

impl_typeck!(self, id: DeclInProcRef => {
	match id {
		DeclInProcRef::Subprog(id)     => self.typeck(id),
		DeclInProcRef::SubprogBody(id) => self.typeck(id),
		DeclInProcRef::SubprogInst(id) => self.typeck(id),
		DeclInProcRef::Pkg(id)         => self.typeck(id),
		DeclInProcRef::PkgBody(id)     => self.typeck(id),
		DeclInProcRef::PkgInst(id)     => self.typeck(id),
		DeclInProcRef::Type(id)        => self.typeck(id),
		DeclInProcRef::Subtype(id)     => self.typeck(id),
		DeclInProcRef::Const(id)       => self.typeck(id),
		DeclInProcRef::Var(id)         => self.typeck(id),
		DeclInProcRef::File(id)        => self.typeck(id),
		DeclInProcRef::Alias(id)       => self.typeck(id),
		DeclInProcRef::Attr(id)        => self.typeck(id),
		DeclInProcRef::AttrSpec(id)    => self.typeck(id),
		DeclInProcRef::GroupTemp(id)   => self.typeck(id),
		DeclInProcRef::Group(id)       => self.typeck(id),
	}
});

impl_typeck!(self, id: ConcStmtRef => {
	match id {
		ConcStmtRef::Block(id)         => self.typeck(id),
		ConcStmtRef::Process(id)       => self.typeck(id),
		ConcStmtRef::ConcProcCall(id)  => self.typeck(id),
		ConcStmtRef::ConcAssert(id)    => self.typeck(id),
		ConcStmtRef::ConcSigAssign(id) => self.typeck(id),
		ConcStmtRef::CompInst(id)      => self.typeck(id),
		ConcStmtRef::ForGen(id)        => self.typeck(id),
		ConcStmtRef::IfGen(id)         => self.typeck(id),
		ConcStmtRef::CaseGen(id)       => self.typeck(id),
	}
});

impl_typeck!(self, id: SeqStmtRef => {
	match id {
		SeqStmtRef::Wait(id)      => self.lazy_typeck(id),
		SeqStmtRef::Assert(id)    => self.lazy_typeck(id),
		SeqStmtRef::Report(id)    => self.lazy_typeck(id),
		SeqStmtRef::SigAssign(id) => self.lazy_typeck(id),
		SeqStmtRef::VarAssign(id) => self.lazy_typeck(id),
		SeqStmtRef::ProcCall(id)  => self.lazy_typeck(id),
		SeqStmtRef::If(id)        => self.lazy_typeck(id),
		SeqStmtRef::Case(id)      => self.lazy_typeck(id),
		SeqStmtRef::Loop(id)      => self.lazy_typeck(id),
		SeqStmtRef::Nexit(id)     => self.lazy_typeck(id),
		SeqStmtRef::Return(id)    => self.lazy_typeck(id),
		SeqStmtRef::Null(id)      => self.lazy_typeck(id),
	}
});

impl_typeck_err!(self, id: SubprogDeclRef => {
	let hir = self.ctx.hir(id)?;
	self.typeck_subprog_spec(&hir.spec);
	Ok(())
});

impl_typeck_err!(self, id: SubprogBodyRef => {
	let hir = self.ctx.hir(id)?;
	self.typeck_subprog_spec(&hir.spec);
	self.typeck_slice(&hir.decls);
	self.typeck_slice(&hir.stmts);
	Ok(())
});

impl_typeck_err!(self, id: SubprogInstRef => {
	let _hir = self.ctx.hir(id)?;
	// self.typeck_slice(&hir.generic_map);
	Ok(())
});

impl_typeck_err!(self, id: ConstDeclRef => {
	self.ctx.lazy_typeval(id)?;
	Ok(())
});

impl_typeck_err!(self, id: SignalDeclRef => {
	self.ctx.lazy_typeval(id)?;
	Ok(())
});

impl_typeck_err!(self, id: VarDeclRef => {
	self.ctx.lazy_typeval(id)?;
	Ok(())
});

impl_typeck_err!(self, id: FileDeclRef => {
	self.ctx.lazy_typeval(id)?;
	Ok(())
});

impl_typeck!(self, id: AliasDeclRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: CompDeclRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: AttrDeclRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: AttrSpecRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: CfgSpecRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: DisconSpecRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: GroupTempRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: GroupDeclRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: BlockStmtRef => {
	unimp!(self, id)
});

impl_typeck_err!(self, id: ProcessStmtRef => {
	let hir = self.ctx.hir(id)?;
	for &decl in &hir.decls {
		self.typeck(decl);
	}
	for &stmt in &hir.stmts {
		self.typeck(stmt);
	}
	Ok(())
});

impl_typeck!(self, id: ConcCallStmtRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: ConcAssertStmtRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: ConcSigAssignStmtRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: CompInstStmtRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: ForGenStmtRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: IfGenStmtRef => {
	unimp!(self, id)
});

impl_typeck!(self, id: CaseGenStmtRef => {
	unimp!(self, id)
});

impl_typeck_err!(self, id: SigAssignStmtRef => {
	let hir = self.ctx.hir(id)?;
	let lhs_ty = match hir.target {
		hir::SigAssignTarget::Name(sig) => self.ctx.ty(sig)?,
		hir::SigAssignTarget::Aggregate => unimpmsg!(self, hir.target_span, "assignment to aggregate signal"),
	};
	// let mut ctx = TypeckContext::new(self);
	// let typeck_dm = |dm| match dm {
	// 	// TODO: typeck time expression
	// 	// &hir::DelayMechanism::RejectInertial(expr) => self.typeck_node(expr, self.intern_ty(/* time type */))?,
	// 	_ => Ok(()),
	// };
	match hir.kind {
		hir::SigAssignKind::SimpleWave(ref dm, ref wave) => {
			self.typeck_delay_mechanism(dm);
			self.typeck_waveform(wave, lhs_ty);
		}
		hir::SigAssignKind::SimpleForce(_, _expr) => {
			// self.typeck_node(expr, lhs_ty)?;
		}
		hir::SigAssignKind::SimpleRelease(_) => (),
		hir::SigAssignKind::CondWave(ref dm, ref _cond) => {
			self.typeck_delay_mechanism(dm);
			// self.typeck_node(cond, lhs_ty)?;
		}
		hir::SigAssignKind::CondForce(_, ref _cond) => {
			// self.typeck_node(cond, lhs_ty)?;
		}
		hir::SigAssignKind::SelWave(ref dm, ref _sel) => {
			self.typeck_delay_mechanism(dm);
			// self.typeck_node(sel, lhs_ty)?;
		}
		hir::SigAssignKind::SelForce(_, ref _sel) => {
			// self.typeck_node(sel, lhs_ty)?;
		}
	}
	Ok(())
});

impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
	/// Replace `Ty::Named` by the actual type definition recursively.
	pub fn deref_named_type<'a>(&self, ty: &'a Ty) -> Result<&'a Ty> where 'ctx: 'a {
		match ty {
			&Ty::Named(_, tmr) => {
				let inner = self.ty(tmr)?;
				self.deref_named_type(inner)
			}
			other => Ok(other)
		}
	}
}


/// Determine the type of a type mark.
impl_make!(self, id: TypeMarkRef => &Ty {
	match id {
		TypeMarkRef::Type(id) => self.make(id),
		TypeMarkRef::Subtype(id) => self.make(id),
	}
});


/// Determine the type of a subtype indication.
#[deprecated]
impl_make!(self, id: SubtypeIndRef => &Ty {
	self.lazy_typeval(id)
	// let hir = self.hir(id)?;
	// let ctx = TypeckContext::new(self);
	// let inner = self.intern_ty(Ty::Named(hir.type_mark.span, hir.type_mark.value));
	// match hir.constraint {
	// 	None => Ok(inner),
	// 	Some(Spanned{ value: hir::Constraint::Range(ref con), span }) => {
	// 		ctx.apply_range_constraint(inner, Spanned::new(con, span))
	// 	}
	// 	Some(Spanned{ value: hir::Constraint::Array(ref ac), span }) => {
	// 		ctx.apply_array_constraint(inner, Spanned::new(ac, span))
	// 	}
	// 	Some(Spanned{ value: hir::Constraint::Record(ref rc), span }) => {
	// 		ctx.apply_record_constraint(inner, Spanned::new(rc, span))
	// 	}
	// }
});


/// Determine the type of a type declaration.
impl_make!(self, id: TypeDeclRef => &Ty {
	let hir = self.hir(id)?;
	let data = match hir.data {
		Some(ref d) => d,
		None => {
			self.emit(
				DiagBuilder2::error(format!("declaration of type `{}` is incomplete", hir.name.value))
				.span(hir.name.span)
			);
			return Err(());
		}
	};
	match data.value {
		hir::TypeData::Range(dir, lb_id, rb_id) => {
			self.make_range_ty(dir, lb_id, rb_id, data.span)
		}

		hir::TypeData::Physical(dir, lb_id, rb_id, ref units, primary_index) => {
			let base = self.make_range_ty(dir, lb_id, rb_id, data.span)?;
			let base = match *base {
				Ty::Int(ref it) => it.clone(),
				_ => unreachable!(),
			};
			let units = units.iter().map(|&(name, ref abs, ref rel)|
				PhysicalUnit::new(name.value, abs.clone(), rel.clone())
			).collect();
			Ok(self.intern_ty(PhysicalTy::new(id, base, units, primary_index)))
		}

		hir::TypeData::Enum(ref lits) => {
			use ty2::{EnumType, EnumLiteral};
			let ty = EnumType::new(lits.iter().map(|l| match *l {
				hir::EnumLit::Ident(sp) => EnumLiteral::from(sp.value),
				hir::EnumLit::Char(sp)  => EnumLiteral::from(sp.value),
			}));
			debugln!("type from enum `{}` = {}", hir.name, ty);
			Ok(self.intern_ty(EnumTy::new(id)))
		}

		hir::TypeData::Access(subty_id) => {
			let ty = self.ty(subty_id)?.clone();
			Ok(self.intern_ty(Ty::Access(Box::new(ty))))
		}

		hir::TypeData::Array(ref index_ids, elem_ty) => {
			// To determine the type of an array, we first need to obtain the
			// HIR of each index. Based on that we can decide whether this is an
			// unbounded or constrained array type, and proceed accordingly.
			let mut had_fails = false;
			let mut indices = Vec::new();
			for &index_id in index_ids {
				let hir = match self.hir(index_id) {
					Ok(h) => h,
					Err(()) => { had_fails = true; continue; }
				};
				indices.push(match hir.value {
					hir::ArrayTypeIndex::Unbounded(tm) => {
						ArrayIndex::Unbounded(Box::new(self.ty(tm.value)?.clone()))
					}
					hir::ArrayTypeIndex::Subtype(subty) => {
						ArrayIndex::Constrained(Box::new(self.ty(subty)?.clone()))
					}
					hir::ArrayTypeIndex::Range(dir, lb_id, rb_id) => {
						ArrayIndex::Constrained(Box::new(
							self.make_range_ty(dir, lb_id, rb_id, hir.span)?.clone()
						))
					}
				});
			}
			if had_fails {
				return Err(());
			}
			let elem_ty = self.ty(elem_ty)?.clone();
			Ok(self.intern_ty(ArrayTy::new(indices, Box::new(elem_ty))))
		}

		hir::TypeData::File(tm) => {
			let inner = self.ty(tm.value)?.clone();
			Ok(self.intern_ty(Ty::File(Box::new(inner))))
		}

		hir::TypeData::Record(ref fields) => {
			let mut had_fails = false;
			let mut mapped_fields = Vec::new();
			let mut used_names = HashMap::new();
			for &(name, subty) in fields {
				if let Some(&span) = used_names.get(&name.value) {
					self.emit(
						DiagBuilder2::error(format!("field `{}` already declared", name.value))
						.span(name.span)
						.add_note("Previous declaration was here:")
						.span(span)
					);
					had_fails = true;
				} else {
					used_names.insert(name.value, name.span);
				}
				mapped_fields.push((name.value, Box::new(self.ty(subty)?.clone())))
			}
			if had_fails {
				return Err(());
			}
			Ok(self.intern_ty(RecordTy::new(mapped_fields)))
		}
	}
});


impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
	pub fn make_range_ty(&self, dir: hir::Dir, lb_id: ExprRef, rb_id: ExprRef, span: Span) -> Result<&'ctx Ty> {
		let lb = self.const_value(lb_id)?;
		let rb = self.const_value(rb_id)?;
		Ok(match (lb, rb) {
			(&Const::Int(ref lb), &Const::Int(ref rb)) => {
				use ty2::{IntegerType, Range};
				let ty = IntegerType::new(Range::with_lower_upper(dir, lb.value.clone(), rb.value.clone()));
				debugln!("type from range `{}` = {}", span.extract(), ty);
				self.intern_ty(IntTy::new(dir, lb.value.clone(), rb.value.clone()).maybe_null())
			}

			(&Const::Float(ref _lb), &Const::Float(ref _rb)) => {
				self.emit(
					DiagBuilder2::error("Float range bounds not yet supported")
					.span(span)
				);
				return Err(());
			}

			_ => {
				self.emit(
					DiagBuilder2::error("Bounds of range are not of the same type")
					.span(span)
				);
				return Err(());
			}
		})
	}
}


/// Determine the type of a subtype declaration.
impl_make!(self, id: SubtypeDeclRef => &Ty {
	let hir = self.hir(id)?;
	self.ty(hir.subty)
});


/// Determine the type of a signal declaration.
// impl_make!(self, id: SignalDeclRef => &Ty {
// 	let hir = self.lazy_hir(id)?;
// 	self.lazy_typeval(hir.decl.ty)
// });


/// Determine the type of an expression.
impl_make!(self, id: ExprRef => &Ty {
	let hir = self.hir(id)?;
	match hir.data {
		hir::ExprData::IntegerLiteral(ref c) => {
			// Integer literals either have a type attached, or they inherit
			// their type from the context.
			if let Some(ref ty) = c.ty {
				return Ok(self.intern_ty(ty.clone()));
			}
			if let Some(ty) = self.type_context_resolved(id)? {
				if let &Ty::Int(_) = self.deref_named_type(ty)? {
					return Ok(ty);
				}
			}
			self.emit(
				DiagBuilder2::error(format!("cannot infer type of `{}` from context", hir.span.extract()))
				.span(hir.span)
			);
			Err(())
		}

		hir::ExprData::FloatLiteral(ref _c) => {
			unimp_err!(self, id);
			// // Float literals either have a type attached, or they inherit their
			// // type from the context.
			// if let Some(ref ty) = c.ty {
			// 	return Ok(self.intern_ty(ty.clone()));
			// }
			// if let Some(ty) = self.type_context_resolved(id)? {
			// 	if let &Ty::Float(_) = self.deref_named_type(ty)? {
			// 		return Ok(ty);
			// 	}
			// }
			// self.emit(
			// 	DiagBuilder2::error("cannot infer type of float literal from context")
			// 	.span(hir.span)
			// );
			// Err(())
		}

		_ => unimp_err!(self, id),
	}
});


/// Determine the type of a typed node.
impl_make!(self, id: TypedNodeRef => &Ty {
	match id {
		TypedNodeRef::SubtypeInd(id) => self.make(id),
		TypedNodeRef::Signal(id)     => self.make(id),
	}
});

impl_make!(self, id: SignalRef => &Ty {
	match id {
		SignalRef::Intf(id) => self.make(id),
		SignalRef::Decl(id) => self.lazy_typeval(id),
	}
});

impl_make!(self, id: IntfObjRef => &Ty {
	match id {
		IntfObjRef::Const(id)  => self.make(id),
		IntfObjRef::Var(id)    => self.make(id),
		IntfObjRef::Signal(id) => self.make(id),
		IntfObjRef::File(id)   => self.make(id),
	}
});

impl_make!(self, id: LatentTypeMarkRef => &Ty {
	self.ty(self.hir(id)?.value)
});

// impl_make!(self, id: LatentSubprogRef => &Ty {
// 	self.ty(self.hir(id)?.value)
// });

// impl_make!(self, id: SubprogRef => &Ty {
// 	match id {
// 		SubprogRef::Decl(id) => self.make(id),
// 		SubprogRef::Inst(id) => self.make(id),
// 	}
// });
