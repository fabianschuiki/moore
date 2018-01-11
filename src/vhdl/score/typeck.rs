// Copyright (c) 2017 Fabian Schuiki

//! This module implements the type calculation of the scoreboard.

use score::*;


impl<'sb, 'ast, 'ctx> ScoreContext<'sb, 'ast, 'ctx> {
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
impl_make!(self, id: SubtypeIndRef => &Ty {
	let hir = self.hir(id)?;
	match hir.constraint {
		hir::Constraint::None => Ok(self.intern_ty(Ty::Named(hir.type_mark.span, hir.type_mark.value))),

		// For range constraints, we first have to check if the constraint is
		// applicable given the type mark. If it is, check if the provided
		// range actually is a proper subtype, and then apply the constraint.
		hir::Constraint::Range(span, expr_id) => {
			let inner = self.deref_named_type(self.ty(hir.type_mark.value)?)?;
			match *inner {
				Ty::Int(ref inner) => {
					// Evaluate the expression to a constant range.
					let range = match *self.const_value(expr_id)? {
						Const::IntRange(ref r) => r,
						ref wrong => {
							self.sess.emit(
								DiagBuilder2::error(format!("{} used to constrain integer type", wrong.kind_desc()))
								.span(span)
							);
							return Err(());
						}
					};

					// Make sure that this is actually a subtype.
					if inner.dir != range.dir || inner.left_bound > range.left_bound.value || inner.right_bound < range.right_bound.value {
						self.sess.emit(
							DiagBuilder2::error(format!("`{}` is not a subrange of `{}`", range, inner))
							.span(span)
						);
						return Err(());
					}

					// Create the new type.
					Ok(self.intern_ty(IntTy::new(inner.dir, range.left_bound.value.clone(), range.right_bound.value.clone()).maybe_null()))
				}

				// All other types we simply cannot constrain by range.
				_ => {
					self.sess.emit(
						DiagBuilder2::error(format!("{} cannot be constrained by range", inner.kind_desc()))
						.span(span)
					);
					return Err(());
				}
			}
		}

		hir::Constraint::Array(ref ac) => {
			self.sess.emit(
				DiagBuilder2::error("Array constraints on subtypes not yet supported")
				.span(ac.span)
			);
			Err(())
		}

		hir::Constraint::Record(ref rc) => {
			self.sess.emit(
				DiagBuilder2::error("Record constraints on subtypes not yet supported")
				.span(rc.span)
			);
			Err(())
		}
	}
});


/// Determine the type of a type declaration.
impl_make!(self, id: TypeDeclRef => &Ty {
	let hir = self.hir(id)?;
	let data = match hir.data {
		Some(ref d) => d,
		None => {
			self.sess.emit(
				DiagBuilder2::error(format!("Declaration of type `{}` is incomplete", hir.name.value))
				.span(hir.name.span)
			);
			return Err(());
		}
	};
	match *data {
		hir::TypeData::Range(span, dir, lb_id, rb_id) => {
			let lb = self.const_value(lb_id)?;
			let rb = self.const_value(rb_id)?;
			Ok(match (lb, rb) {
				(&Const::Int(ref lb), &Const::Int(ref rb)) => {
					self.intern_ty(IntTy::new(dir, lb.value.clone(), rb.value.clone()).maybe_null())
				}

				(&Const::Float(ref _lb), &Const::Float(ref _rb)) => {
					self.sess.emit(
						DiagBuilder2::error("Float range bounds not yet supported")
						.span(span)
					);
					return Err(());
				}

				_ => {
					self.sess.emit(
						DiagBuilder2::error("Bounds of range are not of the same type")
						.span(span)
					);
					return Err(());
				}
			})
		}

		hir::TypeData::Enum(..) => {
			Ok(self.intern_ty(EnumTy::new(id)))
		}
	}
});


/// Determine the type of a subtype declaration.
impl_make!(self, id: SubtypeDeclRef => &Ty {
	let hir = self.hir(id)?;
	self.ty(hir.subty)
});


/// Determine the type of a signal declaration.
impl_make!(self, id: SignalDeclRef => &Ty {
	let hir = self.existing_hir(id)?;
	self.ty(hir.subty)
});


/// Determine the type of an expression.
impl_make!(self, id: ExprRef => &Ty {
	let hir = self.hir(id)?;
	match hir.data {
		_ => panic!("typeck not impl for expr {:?}", hir.data)
	}
});


/// Determine the type of a typed node.
impl_make!(self, id: TypedNodeRef => &Ty {
	match id {
		TypedNodeRef::SubtypeInd(id) => self.make(id),
	}
});
