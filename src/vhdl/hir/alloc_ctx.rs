// Copyright (c) 2016-2021 Fabian Schuiki

use crate::common::errors::*;
use crate::common::score::Result;
use crate::common::source::Spanned;
use crate::common::{SessionContext, Verbosity};

use crate::arenas::Alloc;
use crate::hir::Arenas2;
use crate::scope2::{Def2, ScopeContext, ScopeData};
use crate::score::ResolvableName;

/// A context for HIR node construction.
#[derive(Copy, Clone)]
pub struct AllocContext<'t> {
    pub sess: &'t SessionContext,
    pub arenas: &'t Arenas2<'t>,
    pub scope: &'t ScopeData<'t>,
}

impl<'t> AllocContext<'t> {
    /// Create a subscope and return a new context for that scope.
    pub fn create_subscope(&self) -> AllocContext<'t> {
        AllocContext {
            scope: self.arenas.alloc(ScopeData::new(self.scope)),
            ..*self
        }
    }

    /// Return the current scope.
    pub fn scope(&self) -> &'t ScopeData<'t> {
        self.scope
    }
}

impl<'a, 't, T: 't> Alloc<'a, 't, T> for AllocContext<'t>
where
    Arenas2<'t>: Alloc<'t, 't, T>,
{
    fn alloc(&'a self, value: T) -> &'t mut T {
        self.arenas.alloc(value)
    }
}

impl<'t> ScopeContext<'t> for AllocContext<'t> {
    fn define(&self, name: Spanned<ResolvableName>, def: Def2<'t>) -> Result<()> {
        self.scope.define(name, def, self.sess)
    }

    fn import_def(&self, name: ResolvableName, def: Spanned<Def2<'t>>) -> Result<()> {
        self.scope.import_def(name, def)
    }

    fn import_scope(&self, scope: &'t ScopeData<'t>) -> Result<()> {
        self.scope.import_scope(scope)
    }

    fn resolve(&self, name: ResolvableName, recur: bool) -> Vec<Spanned<Def2<'t>>> {
        self.scope.resolve(name, recur)
    }
}

impl<'t> DiagEmitter for AllocContext<'t> {
    fn emit(&self, diag: DiagBuilder2) {
        self.sess.emit(diag)
    }
}

impl<'t> SessionContext for AllocContext<'t> {
    fn has_verbosity(&self, verb: Verbosity) -> bool {
        self.sess.has_verbosity(verb)
    }
}
