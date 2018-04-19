// Copyright (c) 2018 Fabian Schuiki

//! Arena to allocate HIR nodes into.

use scope2::ScopeData;
use hir::*;

make_arenas!(
    /// An arena to allocate HIR nodes into.
    pub struct Arenas2<'t> {
        scope_data: ScopeData<'t>,

        library: Library<'t>,
        package: Package2<'t>,
        type_decl: TypeDecl2<'t>,
        const_decl: ConstDecl<'t>,
        int_lit_expr: IntLitExpr,

        package_slot: Slot<'t, Package2<'t>>,
        type_decl_slot: Slot<'t, TypeDecl2<'t>>,
        const_decl_slot: Slot<'t, ConstDecl<'t>>,
    }
);
