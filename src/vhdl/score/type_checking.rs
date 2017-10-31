// Copyright (c) 2017 Fabian Schuiki

//! This module implements the type calculation of the scoreboard.

use score::*;


impl<'sb, 'ast, 'ctx> ScoreContext<'sb, 'ast, 'ctx> {
	/// Map a VHDL type to the corresponding LLHD type.
	pub fn map_type(&self, ty: &Ty) -> Result<llhd::Type> {
		let ty = self.deref_named_type(ty)?;
		Ok(match *ty {
			Ty::Named(..) => unreachable!(),
			Ty::Int(ref ty) => {
				let diff = match ty.dir {
					hir::Dir::To => &ty.right_bound - &ty.left_bound,
					hir::Dir::Downto => &ty.left_bound - &ty.right_bound,
				};
				if diff.is_negative() {
					llhd::void_ty()
				} else {
					llhd::int_ty(diff.bits())
				}
			}
		})
	}


	/// Replace `Ty::Named` by the actual type definition recursively.
	#[allow(unreachable_patterns)]
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
	Ok(self.sb.arenas.ty.alloc(Ty::Named(hir.type_mark.span, hir.type_mark.value)))
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
					self.sb.arenas.ty.alloc(IntTy::new(dir, lb.value.clone(), rb.value.clone()).into())
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
	}
});


/// Determine the type of a subtype declaration.
impl_make!(self, _id: SubtypeDeclRef => &Ty {
	unimplemented!()
});


/// Determine the type of a signal declaration.
impl_make!(self, id: SignalDeclRef => &Ty {
	let hir = self.existing_hir(id)?;
	self.ty(hir.subty)
});
