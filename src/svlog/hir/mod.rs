// Copyright (c) 2017 Fabian Schuiki

//! The high-level intermediate representation for SystemVerilog.
//!
//! After parsing the AST is lowered into this representation, eliminating a lot
//! of syntactic sugar and resolving any syntactic ambiguities.

use crate::crate_prelude::*;
use std::{collections::BTreeSet, sync::Arc};

mod lowering;
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
        ports: Port,
        types: Type,
        exprs: Expr,
        inst_target: InstTarget,
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
    }
);

/// Determine the nodes accessed by another node.
pub(crate) fn accessed_nodes<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
) -> Result<Arc<AccessTable>> {
    let mut k = AccessTableCollector {
        cx,
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
    pub read: BTreeSet<NodeId>,
    /// All nodes being written.
    pub written: BTreeSet<NodeId>,
}

/// A visitor for the HIR that populates an access table.
struct AccessTableCollector<'a, C> {
    cx: &'a C,
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
            ExprKind::Ident(name) => match self.cx.resolve_upwards_or_error(name, expr.id) {
                Ok(binding) => {
                    if self.is_binding_interesting(binding) {
                        if lvalue {
                            self.table.written.insert(binding);
                        } else {
                            self.table.read.insert(binding);
                        }
                    }
                }
                Err(()) => (),
            },
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
            Err(_) => return false,
            _ => (),
        }
        true
    }
}
