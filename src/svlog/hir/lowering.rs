// Copyright (c) 2016-2019 Fabian Schuiki

//! Lowering of AST nodes to HIR nodes.

use crate::ast_map::AstNode;
use crate::crate_prelude::*;
use crate::hir::HirNode;

pub(crate) fn hir_of<'gcx>(cx: Context<'gcx>, node_id: NodeId) -> Result<HirNode> {
    debug!("hir_of({})", node_id);

    let ast = cx.ast_of(node_id)?;

    #[allow(unreachable_patterns)]
    match ast {
        AstNode::Module(m) => lower_module(cx, node_id, m),
        _ => {
            cx.emit(
                DiagBuilder2::bug(format!(
                    "lowering to HIR for {} not implemented",
                    ast.desc_full()
                ))
                .span(ast.human_span()),
            );
            Err(())
        }
    }
}

fn lower_module<'gcx>(
    cx: Context<'gcx>,
    node_id: NodeId,
    ast: &ast::ModDecl,
) -> Result<HirNode<'gcx>> {
    let hir = hir::Module {
        id: node_id,
        name: Spanned::new(ast.name, ast.name_span),
        span: ast.span,
    };
    let hir = cx.arenas.alloc_hir(hir);
    Ok(HirNode::Module(hir))
}
