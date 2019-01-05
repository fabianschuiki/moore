// Copyright (c) 2017 Fabian Schuiki

//! The high-level intermediate representation for SystemVerilog. After name
//! resolution, the AST is lowered into this representation, eliminating a lot
//! of the syntactic sugar represented in the AST, and resolving default and
//! implicit values.

mod lowering;
mod nodes;

pub(crate) use self::lowering::hir_of;
pub use self::nodes::*;

make_arenas!(
    /// An arena to allocate HIR nodes into.
    pub struct Arena<'hir> {
        modules: Module<'hir>,
        ports: Port,
    }
);
