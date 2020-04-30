// Copyright (c) 2016-2020 Fabian Schuiki
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

use crate::syntax::ast::{self, NodeId};
use moore_common::name::*;
use moore_common::source::*;
use std;
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub struct SymTbl {
    next_id: usize,
    pub root_scope: Scope,
    libs: HashMap<Name, NodeId>,
    pub scopes: HashMap<NodeId, Scope>,
}

impl SymTbl {
    /// Create a new empty symbol table.
    pub fn new() -> SymTbl {
        SymTbl {
            next_id: 1,
            root_scope: Scope::new(Default::default()),
            libs: HashMap::new(),
            scopes: HashMap::new(),
        }
    }

    /// Allocate a new node ID that has not yet been used.
    pub fn alloc_id(&mut self) -> NodeId {
        let id = NodeId::new(self.next_id);
        self.next_id += 1;
        id
    }

    /// Obtain the node ID for the library with the given name, or allocate a
    /// new ID if none exists yet. Use this function to create a scope for this
    /// library.
    pub fn get_library_id(&mut self, name: Name) -> NodeId {
        // Unfortunately we cannot just use or_insert_with(|| self.alloc_id())
        // here, as this would borrow self twice. So we play a little trick
        // where we check what ID was assigned to the library, and ensure that
        // self.next_id is at least 1 greater than that ID.
        let id = *self.libs.entry(name).or_insert(NodeId::new(self.next_id));
        if id.as_usize() == self.next_id {
            self.next_id += 1;
            self.root_scope.declare(
                Spanned::new(DefName::Ident(name), INVALID_SPAN),
                Def::Lib(id),
            );
        }
        id
    }

    /// Add a scope to the symbol table. If a scope with the same node ID
    /// already exists, the new scope's contents are merged into the existing
    /// scope. This allows for gradual extension of the contents of a scope.
    /// Useful for populating library scopes.
    pub fn add_scope(&mut self, scope: Scope) {
        use std::collections::hash_map::Entry;
        match self.scopes.entry(scope.node_id) {
            Entry::Occupied(e) => {
                e.into_mut().merge(scope);
            }
            Entry::Vacant(e) => {
                e.insert(scope);
            }
        }
    }
}

#[derive(Debug)]
pub struct Scope {
    pub node_id: NodeId,
    pub subscopes: HashSet<NodeId>,
    pub defs: HashMap<DefName, Vec<(Span, Def)>>,
    pub parent_id: Option<NodeId>,
}

impl Scope {
    /// Create a new empty scope for the node with the given ID.
    pub fn new(node_id: NodeId) -> Scope {
        Scope {
            node_id: node_id,
            subscopes: HashSet::new(),
            defs: HashMap::new(),
            parent_id: None,
        }
    }

    /// Merge the contents of another scope into this scope. The scope keeps the
    /// current node ID.
    pub fn merge(&mut self, other: Scope) {
        self.subscopes.extend(other.subscopes);
        for (k, v) in other.defs {
            self.defs.entry(k).or_insert_with(|| Vec::new()).extend(v);
        }
    }

    /// Declare a subscope that is nested within this scope.
    pub fn declare_subscope(&mut self, scope_id: NodeId) {
        assert!(scope_id != Default::default());
        self.subscopes.insert(scope_id);
    }

    /// Declare a name that can be bound to in this scope.
    pub fn declare(&mut self, name: Spanned<DefName>, def: Def) {
        assert!(def.node_id() != Default::default());
        self.defs
            .entry(name.value)
            .or_insert_with(|| Vec::new())
            .push((name.span, def));
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash)]
pub enum DefName {
    Ident(Name),
    Char(char),
    String(Name),
}

impl std::fmt::Display for DefName {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            DefName::Ident(n) => write!(f, "{}", n),
            DefName::Char(n) => write!(f, "'{}'", n),
            DefName::String(n) => write!(f, "\"{}\"", n),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum Def {
    Lib(NodeId),
    Entity(NodeId),
    Cfg(NodeId),
    Pkg(NodeId),
    PkgInst(NodeId),
    Ctx(NodeId),
    Arch(NodeId),
    Const(NodeId),
    Signal(NodeId),
    File(NodeId),
    Var(NodeId),
    Ty(NodeId),
    Subty(NodeId),
    Alias(NodeId),
    Subprog(NodeId),
    Comp(NodeId),
    Attr(NodeId),
    Intf(NodeId),
    Group(NodeId),
    Stmt(NodeId),
}

impl Def {
    /// Obtain the node ID wrapped within the definition.
    pub fn node_id(&self) -> NodeId {
        use self::Def::*;
        match *self {
            Lib(id) | Entity(id) | Cfg(id) | Pkg(id) | PkgInst(id) | Ctx(id) | Arch(id)
            | Const(id) | Signal(id) | File(id) | Var(id) | Ty(id) | Subty(id) | Alias(id)
            | Subprog(id) | Comp(id) | Attr(id) | Intf(id) | Group(id) | Stmt(id) => id,
        }
    }
}

// /// Converts a primary name to a definition name that can be stored in a scope.
pub fn def_name_from_primary_name(name: &ast::PrimaryName) -> Spanned<DefName> {
    Spanned::new(
        match name.kind {
            ast::PrimaryNameKind::Ident(n) => DefName::Ident(n),
            ast::PrimaryNameKind::Char(n) => DefName::Char(n),
            ast::PrimaryNameKind::String(n) => DefName::String(n),
        },
        name.span,
    )
}
