// Copyright (c) 2018 Fabian Schuiki

use common::SessionContext;
use common::source::Spanned;
use common::errors::*;
use common::score::Result;

use arenas::{Alloc, AllocInto};
use score::ResolvableName;
use scope2::{Def2, ScopeContext, ScopeData};
use hir::Arenas2;

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

impl<'t, T> AllocInto<'t, T> for AllocContext<'t>
where
    Arenas2<'t>: Alloc<T>,
{
    fn alloc(&self, value: T) -> &'t mut T {
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
