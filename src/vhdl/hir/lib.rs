// Copyright (c) 2018 Fabian Schuiki

use common::name::Name;
use common::source::{Span, INVALID_SPAN};
use common::score::Result;

use syntax::ast;
use hir::visit::Visitor;
use hir::{Context, FromAst, LatentNode, Node, Package2};

/// A library.
pub struct Library<'t> {
    name: Name,
    units: Vec<&'t LatentNode<'t, Node<'t>>>,
}

impl<'t> Library<'t> {
    pub fn new(name: Name, units: &[&'t ast::DesignUnit], ctx: Context<'t>) -> Result<Self> {
        // ctx.define()
        let units = units
            .into_iter()
            .flat_map(|unit| -> Option<&'t LatentNode<'t, Node>> {
                match unit.data {
                    ast::DesignUnitData::PkgDecl(ref decl) => {
                        Some(Package2::alloc_slot(decl, ctx).ok()?)
                    }
                    _ => None,
                }
            })
            .collect();
        Ok(Library {
            name: name,
            units: units,
        })
    }

    /// Return the name of the library.
    pub fn name(&self) -> Name {
        self.name
    }

    /// Return a slice of the design units in this library.
    pub fn units(&self) -> &[&'t LatentNode<'t, Node<'t>>] {
        &self.units
    }
}

impl<'t> Node<'t> for Library<'t> {
    fn span(&self) -> Span {
        INVALID_SPAN
    }

    fn desc_kind(&self) -> String {
        "library".into()
    }

    fn desc_name(&self) -> String {
        format!("library `{}`", self.name)
    }

    fn accept(&'t self, visitor: &mut Visitor<'t>) {
        visitor.visit_library(self);
    }

    fn walk(&'t self, visitor: &mut Visitor<'t>) {
        for u in &self.units {
            u.accept(visitor);
        }
    }
}
