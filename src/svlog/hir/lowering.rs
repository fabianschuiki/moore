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
                    "lowering of {} to hir not implemented",
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
    ast: &'gcx ast::ModDecl,
) -> Result<HirNode<'gcx>> {
    let mut ports = Vec::new();
    for port in &ast.ports {
        match *port {
            ast::Port::Named { .. } => {
                let id = cx.alloc_id(port.human_span());
                cx.set_ast(id, AstNode::Port(port));
                ports.push(id);
            }
            _ => return cx.unimp(port),
        }
    }
    let hir = hir::Module {
        id: node_id,
        name: Spanned::new(ast.name, ast.name_span),
        span: ast.span,
        ports: cx.arenas.alloc_ids(ports),
    };
    Ok(HirNode::Module(cx.arenas.alloc_hir(hir)))
}
