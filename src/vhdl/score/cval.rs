// Copyright (c) 2017 Fabian Schuiki

//! This module implements constant value computation.

use score::*;


// Calculate the constant value of an expression.
impl_make!(self, id: ExprRef => &Const {
	let hir = self.hir(id)?;
	Ok(match hir.data {
		// Integer literals.
		hir::ExprData::IntegerLiteral(ref c) => self.sb.arenas.konst.alloc(Const::from(c.clone())),

		// Float literals.
		hir::ExprData::FloatLiteral(ref c) => self.sb.arenas.konst.alloc(Const::from(c.clone())),

		// Unary operators.
		hir::ExprData::Unary(op, arg_id) => {
			let arg = self.const_value(arg_id)?;
			// TODO: Lookup the type of the current expression and perform
			// the operation accordingly.
			match op {
				hir::UnaryOp::Pos => arg,
				hir::UnaryOp::Neg => self.sb.arenas.konst.alloc(arg.negate()),
				_ => unimplemented!()
			}
		}

		// Ranges.
		hir::ExprData::Range(dir, lb_id, rb_id) => {
			// TODO: Determine the type of ourself, then make sure the const
			// values are all cast appropriately.
			let lb = self.const_value(lb_id)?;
			let rb = self.const_value(rb_id)?;
			match (lb, rb) {
				(&Const::Int(ref lb), &Const::Int(ref rb)) => {
					self.intern_const(ConstIntRange::new(dir, lb.clone(), rb.clone()))
				}
				(&Const::Float(ref lb), &Const::Float(ref rb)) => {
					self.intern_const(ConstFloatRange::new(dir, lb.clone(), rb.clone()))
				}
				_ => {
					self.sess.emit(
						DiagBuilder2::error("left and right bound of range must both be integer or float")
						.span(hir.span)
					);
					return Err(());
				}
			}
		}

		// All other expressions cannot be turned into a constant value.
		_ => {
			self.sess.emit(
				DiagBuilder2::error("expression does not have a constant value")
				.span(hir.span)
			);
			return Err(());
		}
	})
});
