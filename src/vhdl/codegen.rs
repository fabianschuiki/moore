// Copyright (c) 2017 Fabian Schuiki

//! This module implements the code generation for VHDL.

use moore_common::score::Result;
use score::*;
// use hir;
use llhd;


pub trait Codegen<I,C> {
	fn codegen(&self, id: I, ctx: &mut C) -> Result<()>;
}


/// This macro implements the `Codegen` trait for a specific combination of
/// identifier and context types.
macro_rules! impl_codegen {
	($self:tt, $id:ident: $id_ty:ty, $ctx:ident: &mut $ctx_ty:ty => $blk:block) => {
		impl<'sb, 'ast, 'ctx> Codegen<$id_ty, $ctx_ty> for ScoreContext<'sb, 'ast, 'ctx> {
			fn codegen(&$self, $id: $id_ty, $ctx: &mut $ctx_ty) -> Result<()> $blk
		}
	}
}


impl_codegen!(self, id: DeclInBlockRef, ctx: &mut llhd::Entity => {
	match id {
		DeclInBlockRef::Pkg(_id)           => Ok(()),
		DeclInBlockRef::PkgInst(_id)       => Ok(()),
		DeclInBlockRef::Type(_id)          => Ok(()),
		DeclInBlockRef::Subtype(_id)       => Ok(()),
		DeclInBlockRef::Const(id)          => self.codegen(id, ctx),
		DeclInBlockRef::Signal(id)         => self.codegen(id, ctx),
		DeclInBlockRef::SharedVariable(id) => self.codegen(id, ctx),
		DeclInBlockRef::File(id)           => self.codegen(id, ctx),
	}
});


impl_codegen!(self, _id: ConstDeclRef, _ctx: &mut llhd::Entity => {
	unimplemented!();
});


impl_codegen!(self, id: SignalDeclRef, _ctx: &mut llhd::Entity => {
	// Determine the type of the signal.
	let hir = self.existing_hir(id)?;
	let ty = self.ty(id)?;

	// Calculate the initial value for the signal, either from the provided
	// expression or implicitly.
	let init = if let Some(init_id) = hir.init {
		self.const_value(init_id)?
	} else {
		self.default_value_for_type(&ty)?
	};

	println!("signal {:?}, type {:?}, init {:?}", id, ty, init);

	Ok(())
});


impl_codegen!(self, _id: SharedVariableDeclRef, _ctx: &mut llhd::Entity => {
	unimplemented!();
});


impl_codegen!(self, _id: FileDeclRef, _ctx: &mut llhd::Entity => {
	unimplemented!();
});
