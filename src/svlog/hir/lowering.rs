// Copyright (c) 2016-2019 Fabian Schuiki

//! Lowering of AST nodes to HIR nodes.

use crate::{ast_map::AstNode, crate_prelude::*, hir::HirNode};

pub(crate) fn hir_of<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<HirNode<'gcx>> {
    let ast = cx.ast_of(node_id)?;

    #[allow(unreachable_patterns)]
    match ast {
        AstNode::Module(m) => lower_module(cx, node_id, m),
        AstNode::Port(p) => lower_port(cx, node_id, p),
        AstNode::Type(ty) => {
            let kind = match ty.data {
                ast::VoidType => hir::TypeKind::Builtin(hir::BuiltinType::Void),
                ast::BitType => hir::TypeKind::Builtin(hir::BuiltinType::Bit),
                ast::LogicType => hir::TypeKind::Builtin(hir::BuiltinType::Logic),
                _ => return cx.unimp(ty),
            };
            let hir = hir::Type {
                id: node_id,
                span: ty.span,
                kind: kind,
            };
            Ok(HirNode::Type(cx.arena().alloc_hir(hir)))
        }
        _ => cx.unimp_msg("lowering of", &ast),
    }
}

fn lower_module<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    ast: &'gcx ast::ModDecl,
) -> Result<HirNode<'gcx>> {
    let mut ports = Vec::new();
    for port in &ast.ports {
        match *port {
            ast::Port::Named { .. } => ports.push(cx.map_ast(AstNode::Port(port))),
            _ => return cx.unimp(port),
        }
    }
    let hir = hir::Module {
        id: node_id,
        name: Spanned::new(ast.name, ast.name_span),
        span: ast.span,
        ports: cx.arena().alloc_ids(ports),
    };
    Ok(HirNode::Module(cx.arena().alloc_hir(hir)))
}

fn lower_port<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    ast: &'gcx ast::Port,
) -> Result<HirNode<'gcx>> {
    let hir = match *ast {
        ast::Port::Named {
            span,
            name,
            dir,
            ref ty,
            ..
        } => hir::Port {
            id: node_id,
            name: Spanned::new(name.name, name.span),
            span: span,
            dir: dir.expect("port missing direction"),
            ty: cx.map_ast(AstNode::Type(ty)),
        },
        _ => return cx.unimp(ast),
    };
    Ok(HirNode::Port(cx.arena().alloc_hir(hir)))
}
