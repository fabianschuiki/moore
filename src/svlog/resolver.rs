// Copyright (c) 2016-2019 Fabian Schuiki

//! Name resolution.
//!
//! This module implements the infrastructure to describe scopes and resolve
//! names in them.

use crate::{ast_map::AstNode, crate_prelude::*, hir::HirNode, ParamEnv};
use std::collections::HashMap;

/// One local scope.
///
/// A rib represents a any kind of scope. Ribs form a tree structure along their
/// parents that may be traversed from the bottom to the top to perform name
/// resolution, or top to bottom to lookup hierarchical names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rib {
    /// The node this rib is associated with.
    ///
    /// When querying the compiler for a node's rib, what you get in return is
    /// not necessarily the rib of that node. If the node does not generate a
    /// new rib, you get back the rib of a parent node.
    pub node: NodeId,
    /// The parent rib.
    ///
    /// Note that this does not necessarily correspond to the parent node, but
    /// may skip nodes that do not contain a rib.
    pub parent: Option<NodeId>,
    /// The data associated with the rib.
    pub kind: RibKind,
}

/// A local scope kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RibKind {
    /// A normal declaration.
    Normal(Spanned<Name>, NodeId),
    /// A module.
    Module(HashMap<Name, NodeId>),
}

impl Rib {
    /// Look up a name.
    pub fn get(&self, name: Name) -> Option<NodeId> {
        self.kind.get(name)
    }
}

impl RibKind {
    /// Look up a name.
    pub fn get(&self, name: Name) -> Option<NodeId> {
        match *self {
            RibKind::Normal(n, id) if n.value == name => Some(id),
            RibKind::Module(ref defs) => defs.get(&name).cloned(),
            _ => None,
        }
    }
}

/// Determine the local rib that applies to a node.
///
/// This will return either the rib the node itself generates, or the next rib
/// up the hierarchy.
pub(crate) fn local_rib<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<&'gcx Rib> {
    let ast = cx.ast_of(node_id)?;
    let kind = match ast {
        AstNode::TypeParam(_, decl) => {
            RibKind::Normal(Spanned::new(decl.name.name, decl.name.span), node_id)
        }
        AstNode::ValueParam(_, decl) => {
            RibKind::Normal(Spanned::new(decl.name.name, decl.name.span), node_id)
        }
        AstNode::Module(_) => RibKind::Module(HashMap::new()),
        AstNode::VarDecl(decl, _, _) => {
            RibKind::Normal(Spanned::new(decl.name, decl.name_span), node_id)
        }
        AstNode::GenvarDecl(decl) => {
            RibKind::Normal(Spanned::new(decl.name, decl.name_span), node_id)
        }
        _ => {
            return cx.local_rib(
                cx.parent_node_id(node_id)
                    .expect("root node must produce a rib"),
            );
        }
    };
    let rib = Rib {
        node: node_id,
        parent: match cx.parent_node_id(node_id) {
            Some(parent_id) => Some(cx.local_rib(parent_id)?.node),
            None => None,
        },
        kind: kind,
    };
    Ok(cx.arena().alloc_rib(rib))
}

/// Resolve a name upwards through the ribs.
///
/// This is equivalent to performing regular scoped namespace lookup.
pub(crate) fn resolve_upwards<'gcx>(
    cx: &impl Context<'gcx>,
    name: Name,
    start_at: NodeId,
) -> Result<Option<NodeId>> {
    let mut next_id = Some(start_at);
    while let Some(rib_id) = next_id {
        let rib = cx.local_rib(rib_id)?;
        if let id @ Some(_) = rib.get(name) {
            return Ok(id);
        }
        next_id = rib.parent;
    }
    Ok(None)
}

/// Resolve a node to its target.
pub(crate) fn resolve_node<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    _env: ParamEnv,
) -> Result<NodeId> {
    let hir = cx.hir_of(node_id)?;
    match hir {
        HirNode::Expr(expr) => match expr.kind {
            hir::ExprKind::Ident(ident) => return cx.resolve_upwards_or_error(ident, node_id),
            _ => (),
        },
        _ => (),
    }
    panic!("cannot resolve {:?}", hir)
}
