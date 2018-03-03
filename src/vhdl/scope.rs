// Copyright (c) 2018 Fabian Schuiki

//! Facilities to manage declarations and resolve names.

#![deny(missing_docs)]

use std::collections::{HashMap, HashSet};

use common::errors::*;
use common::score::Result;
use common::source::Spanned;

use score::{ScoreContext, ScopeRef, Def, ResolvableName};

/// A scope.
pub struct Scope {
    /// The parent scope.
    pub parent: Option<ScopeRef>,

    /// The definitions made in this scope.
    pub defs: HashMap<ResolvableName, Vec<Spanned<Def>>>,

    /// The definitions imported from other scopes.
    pub imported_defs: HashMap<ResolvableName, Vec<Spanned<Def>>>,

    /// The explicitly imported scopes.
    pub imported_scopes: HashSet<ScopeRef>,
}

impl Scope {
    /// Create a new empty scope.
    pub fn new(parent: Option<ScopeRef>) -> Scope {
        Scope {
            parent: parent,
            defs: HashMap::new(),
            imported_defs: HashMap::new(),
            imported_scopes: HashSet::new(),
        }
    }
}

impl<'lazy, 'sb, 'ast, 'ctx> ScoreContext<'lazy, 'sb, 'ast, 'ctx> {
    /// Lookup a scope and perform an operation on it.
    pub fn with_scope<F,R>(&self, scope: ScopeRef, f: F) -> Result<R>
        where F: FnOnce(&mut Scope) -> Result<R>
    {
        let mut tbl = self.sb.scope2_table.borrow_mut();
        let scp = match tbl.get_mut(&scope) {
            Some(s) => s,
            None => {
                self.emit(
                    DiagBuilder2::bug(format!("scope {:?} does not exist`", scope))
                );
                return Err(());
            }
        };
        f(scp)
    }

    /// Define a new name in a scope.
    pub fn define(&self, scope: ScopeRef, name: Spanned<ResolvableName>, def: Def) -> Result<()> {
        self.with_scope(scope, |scope| match def {
            // Handle overloadable cases.
            Def::Enum(_) => {
                scope.defs
                    .entry(name.value)
                    .or_insert_with(|| Vec::new())
                    .push(Spanned::new(def, name.span));
                Ok(())
            },

            // Handle unique cases.
            _ => {
                let ins = scope.defs.insert(name.value, vec![Spanned::new(def, name.span)]);
                if let Some(existing) = ins {
                    self.emit(
                        DiagBuilder2::error(format!("`{}` has already been declared", name.value))
                        .span(name.span)
                        .add_note("Previous declaration was here:")
                        .span(existing.last().unwrap().span)
                    );
                    Err(())
                } else {
                    Ok(())
                }
            }
        })
    }

    /// Import a definition into a scope.
    pub fn import_def(&self, scope: ScopeRef, name: Spanned<ResolvableName>, def: Def) -> Result<()> {
        self.with_scope(scope, |scope|{
            scope.imported_defs
                .entry(name.value)
                .or_insert_with(|| Vec::new())
                .push(Spanned::new(def, name.span));
            Ok(())
        })
    }

    /// Import an entire scope into another scope.
    pub fn import_scope(&self, scope: ScopeRef, into: ScopeRef) -> Result<()> {
        self.with_scope(into, |into|{
            into.imported_scopes.insert(scope);
            Ok(())
        })
    }
}
