// Copyright (c) 2016-2020 Fabian Schuiki

//! The high-level intermediate representation for SystemVerilog.
//!
//! After parsing the AST is lowered into this representation, eliminating a lot
//! of syntactic sugar and resolving any syntactic ambiguities.

use crate::crate_prelude::*;
use std::{collections::BTreeSet, sync::Arc};

pub(crate) mod lowering;
mod nodes;
mod visit;

pub(crate) use self::lowering::hir_of;
pub use self::lowering::Hint;
pub use self::nodes::*;
pub use self::visit::*;

make_arenas!(
    /// An arena to allocate HIR nodes into.
    pub struct Arena<'hir> {
        modules: Module<'hir>,
        interfaces: Interface<'hir>,
        ports: Port,
        types: Type,
        exprs: Expr<'hir>,
        inst_target: InstTarget<'hir>,
        insts: Inst<'hir>,
        type_params: TypeParam,
        value_params: ValueParam,
        var_decls: VarDecl,
        procs: Proc,
        stmts: Stmt,
        event_exprs: EventExpr,
        gens: Gen,
        genvar_decls: GenvarDecl,
        typedefs: Typedef,
        assigns: Assign,
        packages: Package,
        enum_variants: EnumVariant,
        subroutines: Subroutine,
    }
);

/// Determine the nodes accessed by another node.
#[moore_derive::query]
pub(crate) fn accessed_nodes<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Arc<AccessTable>> {
    let mut k = AccessTableCollector {
        cx,
        env,
        table: AccessTable {
            node_id,
            read: Default::default(),
            written: Default::default(),
        },
    };
    k.visit_node_with_id(node_id, false);
    Ok(Arc::new(k.table))
}

/// A table of accessed nodes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccessTable {
    /// The node for which the analysis was performed.
    pub node_id: NodeId,
    /// All nodes being read.
    pub read: BTreeSet<AccessedNode>,
    /// All nodes being written.
    pub written: BTreeSet<AccessedNode>,
}

/// An accessed node. The `AccessTable` carries this enum as entries.
///
/// The `AccessTable` collects accessed nodes across a design. Most of the nodes
/// are pretty simple, but some -- like an interface signal -- require special
/// care.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum AccessedNode {
    /// A regular value.
    Regular(NodeId),
    /// An interface signal.
    Intf(NodeId, NodeId),
}

impl AccessedNode {
    /// Get the ID of the accessed node, dropping any context information.
    pub fn id(&self) -> NodeId {
        match *self {
            Self::Regular(id) | Self::Intf(_, id) => id,
        }
    }
}

impl From<NodeId> for AccessedNode {
    fn from(other: NodeId) -> Self {
        Self::Regular(other)
    }
}

/// A visitor for the HIR that populates an access table.
struct AccessTableCollector<'a, C> {
    cx: &'a C,
    env: ParamEnv,
    table: AccessTable,
}

impl<'a, 'gcx: 'a, C> Visitor<'gcx> for AccessTableCollector<'a, C>
where
    C: Context<'gcx>,
{
    type Context = C;
    fn context(&self) -> &C {
        self.cx
    }

    fn visit_expr(&mut self, expr: &'gcx Expr, lvalue: bool) {
        match expr.kind {
            ExprKind::PositionalPattern(ref nodes) => {
                for &node in nodes {
                    self.visit_node_with_id(node, false);
                }
                return;
            }
            ExprKind::RepeatPattern(node, ref nodes) => {
                self.visit_node_with_id(node, false);
                for &node in nodes {
                    self.visit_node_with_id(node, false);
                }
                return;
            }
            ExprKind::NamedPattern(ref pats) => {
                for &(_, node) in pats {
                    self.visit_node_with_id(node, false);
                }
                return;
            }
            ExprKind::Ident(name) => match self.cx.resolve_upwards_or_error(name, expr.id) {
                Ok(binding) => {
                    if self.is_binding_interesting(binding) {
                        if lvalue {
                            self.table.written.insert(binding.into());
                        } else {
                            self.table.read.insert(binding.into());
                        }
                    }
                }
                Err(()) => (),
            },
            ExprKind::LocalIntfSignal { inst, name } => {
                let node = self
                    .cx
                    .type_of(inst.id(), self.env)
                    .map(|ty| ty.get_interface().unwrap())
                    .and_then(|intf| {
                        self.cx
                            .resolve_hierarchical_or_error(name, intf)
                            .map(|def| AccessedNode::Intf(inst.id(), def.node.id()))
                    });
                match node {
                    Ok(node) => {
                        if lvalue {
                            self.table.written.insert(node);
                        } else {
                            self.table.read.insert(node);
                        }
                    }
                    Err(()) => (),
                }
            }
            _ => (),
        }
        walk_expr(self, expr, lvalue)
    }
}

impl<'a, 'gcx: 'a, C> AccessTableCollector<'a, C>
where
    C: Context<'gcx>,
{
    fn is_binding_interesting(&self, binding: NodeId) -> bool {
        if self.cx.is_parent_of(self.table.node_id, binding) {
            return false;
        }
        match self.cx.hir_of(binding) {
            Ok(HirNode::ValueParam(..)) => return false,
            Ok(HirNode::TypeParam(..)) => return false,
            Ok(HirNode::GenvarDecl(..)) => return false,
            Ok(HirNode::EnumVariant(..)) => return false,
            Ok(HirNode::Package(..)) => return false,
            Ok(HirNode::Module(..)) => return false,
            Err(_) => return false,
            _ => (),
        }
        true
    }
}
