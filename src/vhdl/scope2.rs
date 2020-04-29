// Copyright (c) 2018 Fabian Schuiki

//! Facilities to manage declarations and resolve names.
//!
//! TODO: Replace `scope` with this module.

#![deny(missing_docs)]

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::common::errors::*;
use crate::common::score::Result;
use crate::common::source::Spanned;
use crate::common::{SessionContext, Verbosity};

use crate::hir::{self, Node};
use crate::score::ResolvableName;

/// A definition.
#[derive(Copy, Clone)]
pub enum Def2<'t> {
    /// Any node.
    Node(&'t hir::LatentNode<'t, Node<'t>>),
    /// A library.
    Lib(&'t hir::Library<'t>),
    /// A package.
    Pkg(&'t hir::LatentNode<'t, hir::Package2<'t>>),
    /// A type declaration.
    Type(&'t hir::LatentNode<'t, hir::TypeDecl2<'t>>),
    /// An enumeration type variant.
    Enum(TypeVariantDef<'t>),
    /// A physical type unit.
    Unit(TypeVariantDef<'t>),
}

impl<'t> fmt::Debug for Def2<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Def2::Node(x) => write!(f, "Node({:?})", x as *const _),
            Def2::Lib(x) => write!(f, "Lib({:?})", x as *const _),
            Def2::Pkg(x) => write!(f, "Pkg({:?})", x as *const _),
            Def2::Type(x) => write!(f, "Type({:?})", x as *const _),
            Def2::Enum(x) => write!(f, "Enum({:?}, {})", x.0 as *const _, x.1),
            Def2::Unit(x) => write!(f, "Unit({:?}, {})", x.0 as *const _, x.1),
        }
    }
}

impl<'t> Def2<'t> {
    /// Describe the kind of node the definition points to.
    // TODO: Implement the entire `Node` trait here.
    pub fn desc_kind(&self) -> String {
        match *self {
            Def2::Node(x) => x.poll().unwrap().desc_kind(),
            Def2::Lib(x) => x.desc_kind(),
            Def2::Pkg(x) => x.poll().unwrap().desc_kind(),
            Def2::Type(x) => x.poll().unwrap().desc_kind(),
            Def2::Enum(x) => x.0.poll().unwrap().desc_kind(),
            Def2::Unit(x) => x.0.poll().unwrap().desc_kind(),
        }
    }
}

impl<'t> PartialEq for Def2<'t> {
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Def2::Node(a), Def2::Node(b)) => (a as *const _ == b as *const _),
            (Def2::Lib(a), Def2::Lib(b)) => (a as *const _ == b as *const _),
            (Def2::Pkg(a), Def2::Pkg(b)) => (a as *const _ == b as *const _),
            (Def2::Type(a), Def2::Type(b)) => (a as *const _ == b as *const _),
            (Def2::Enum(a), Def2::Enum(b)) => (a == b),
            (Def2::Unit(a), Def2::Unit(b)) => (a == b),
            _ => false,
        }
    }
}

impl<'t> Eq for Def2<'t> {}

/// A scope.
#[derive(Clone, Debug)]
pub struct ScopeData<'t> {
    /// The parent scope.
    pub parent: Option<&'t ScopeData<'t>>,

    /// The definitions made in this scope.
    pub defs: RefCell<HashMap<ResolvableName, Vec<Spanned<Def2<'t>>>>>,

    /// The definitions imported from other scopes.
    pub imported_defs: RefCell<HashMap<ResolvableName, Vec<Spanned<Def2<'t>>>>>,

    /// The explicitly imported scopes.
    pub imported_scopes: RefCell<HashSet<&'t ScopeData<'t>>>,
}

impl<'t> ScopeData<'t> {
    /// Create a new root scope.
    pub fn root() -> ScopeData<'t> {
        ScopeData {
            parent: None,
            defs: RefCell::new(HashMap::new()),
            imported_defs: RefCell::new(HashMap::new()),
            imported_scopes: RefCell::new(HashSet::new()),
        }
    }

    /// Create a new scope.
    pub fn new(parent: &'t ScopeData<'t>) -> ScopeData<'t> {
        ScopeData {
            parent: Some(parent),
            ..Self::root()
        }
    }

    /// Define a new name in the scope.
    pub fn define(
        &self,
        name: Spanned<ResolvableName>,
        def: Def2<'t>,
        ctx: &SessionContext,
    ) -> Result<()> {
        if ctx.has_verbosity(Verbosity::NAMES) {
            ctx.emit(
                DiagBuilder2::note(format!("define `{}` as {:?}", name.value, def)).span(name.span),
            );
        }
        debugln!("define `{}` as {:?}", name.value, def);
        match def {
            // Handle overloadable cases.
            Def2::Enum(..) => {
                self.defs
                    .borrow_mut()
                    .entry(name.value)
                    .or_insert_with(|| Vec::new())
                    .push(Spanned::new(def, name.span));
                Ok(())
            }

            // Handle unique cases.
            _ => {
                let ins = self
                    .defs
                    .borrow_mut()
                    .insert(name.value, vec![Spanned::new(def, name.span)]);
                if let Some(existing) = ins {
                    ctx.emit(
                        DiagBuilder2::error(format!("`{}` has already been declared", name.value))
                            .span(name.span)
                            .add_note("Previous declaration was here:")
                            .span(existing.last().unwrap().span),
                    );
                    Err(())
                } else {
                    Ok(())
                }
            }
        }
    }

    /// Import a definition into the scope.
    pub fn import_def(&self, name: ResolvableName, def: Spanned<Def2<'t>>) -> Result<()> {
        self.imported_defs
            .borrow_mut()
            .entry(name)
            .or_insert_with(|| Vec::new())
            .push(def);
        Ok(())
    }

    /// Import an entire scope into the scope.
    pub fn import_scope(&self, scope: &'t ScopeData<'t>) -> Result<()> {
        self.imported_scopes.borrow_mut().insert(scope);
        Ok(())
    }

    /// Find a name in this scope.
    ///
    /// This only searches this scope and does not proceed to parent or child
    /// scopes. Use a dedicated name resolver for that.
    pub fn resolve(&self, name: ResolvableName, recur: bool) -> Vec<Spanned<Def2<'t>>> {
        let mut found = Vec::new();
        found.extend(
            self.defs
                .borrow()
                .get(&name)
                .into_iter()
                .flat_map(|d| d.iter()),
        );
        found.extend(
            self.imported_defs
                .borrow()
                .get(&name)
                .into_iter()
                .flat_map(|d| d.iter()),
        );
        for s in self.imported_scopes.borrow().iter() {
            found.extend(
                s.defs
                    .borrow()
                    .get(&name)
                    .into_iter()
                    .flat_map(|d| d.iter()),
            );
        }
        if found.is_empty() && self.parent.is_some() {
            self.parent.unwrap().resolve(name, recur)
        } else {
            found
        }
    }
}

impl<'t> PartialEq for &'t ScopeData<'t> {
    fn eq(&self, b: &Self) -> bool {
        (*self) as *const _ == (*b) as *const _
    }
}
impl<'t> Eq for &'t ScopeData<'t> {}

impl<'t> Hash for &'t ScopeData<'t> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        Hash::hash(&((*self) as *const _), hasher)
    }
}

/// Define names and perform name resolution.
pub trait ScopeContext<'t> {
    /// Define a new name in the scope.
    fn define(&self, name: Spanned<ResolvableName>, def: Def2<'t>) -> Result<()>;
    /// Import a definition into the scope.
    fn import_def(&self, name: ResolvableName, def: Spanned<Def2<'t>>) -> Result<()>;
    /// Import an entire scope into the scope.
    fn import_scope(&self, scope: &'t ScopeData<'t>) -> Result<()>;
    /// Find a name in this scope.
    fn resolve(&self, name: ResolvableName, recur: bool) -> Vec<Spanned<Def2<'t>>>;
}

/// An enumeration variant or physical unit.
#[derive(Copy, Clone)]
pub struct TypeVariantDef<'t>(pub &'t hir::LatentNode<'t, hir::TypeDecl2<'t>>, pub usize);

impl<'t> fmt::Debug for TypeVariantDef<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TypeVariantDef({:?}, {})", self.0 as *const _, self.1)
    }
}

impl<'t> PartialEq for TypeVariantDef<'t> {
    fn eq(&self, other: &Self) -> bool {
        self.0 as *const _ == other.0 as *const _ && self.1 == other.1
    }
}

impl<'t> Eq for TypeVariantDef<'t> {}
