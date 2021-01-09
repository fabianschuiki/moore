// Copyright (c) 2016-2021 Fabian Schuiki

//! Arena to allocate HIR nodes into.

use crate::hir::*;
use crate::scope2::ScopeData;

make_arenas!(
    /// An arena to allocate HIR nodes into.
    pub struct Arenas2<'t> {
        scope_data: ScopeData<'t>,

        library: Library<'t>,
        package: Package2<'t>,
        type_decl: TypeDecl2<'t>,
        subtype_ind: SubtypeInd2<'t>,
        const_decl: ConstDecl<'t>,
        lit_expr: LitExpr,

        package_slot: Slot<'t, Package2<'t>>,
        type_decl_slot: Slot<'t, TypeDecl2<'t>>,
        subtype_ind_slot: Slot<'t, SubtypeInd2<'t>>,
        const_decl_slot: Slot<'t, ConstDecl<'t>>,
    }
);
