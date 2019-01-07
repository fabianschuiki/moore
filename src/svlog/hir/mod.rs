// Copyright (c) 2017 Fabian Schuiki

//! The high-level intermediate representation for SystemVerilog.
//!
//! After parsing the AST is lowered into this representation, eliminating a lot
//! of syntactic sugar and resolving any syntactic ambiguities.

mod lowering;
mod nodes;

pub(crate) use self::lowering::hir_of;
pub use self::lowering::Hint;
pub use self::nodes::*;

make_arenas!(
    /// An arena to allocate HIR nodes into.
    pub struct Arena<'hir> {
        modules: Module<'hir>,
        ports: Port,
        types: Type,
        inst_target: InstTarget,
        insts: Inst<'hir>,
        type_params: TypeParam,
    }
);
