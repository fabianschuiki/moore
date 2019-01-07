// Copyright (c) 2016-2019 Fabian Schuiki

//! Lowering of AST nodes to HIR nodes.

use crate::{ast_map::AstNode, crate_prelude::*, hir::HirNode};

/// A hint about how a node should be lowered to HIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Hint {
    /// Lower as type.
    Type,
    /// Lower as expression.
    Expr,
}

pub(crate) fn hir_of<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<HirNode<'gcx>> {
    let ast = cx.ast_of(node_id)?;

    #[allow(unreachable_patterns)]
    match ast {
        AstNode::Module(m) => lower_module(cx, node_id, m),
        AstNode::Port(p) => lower_port(cx, node_id, p),
        AstNode::TypeOrExpr(&ast::TypeOrExpr::Type(ref ty))
            if cx.lowering_hint(node_id) == Some(Hint::Type) =>
        {
            lower_type(cx, node_id, ty)
        }
        AstNode::Type(ty) => lower_type(cx, node_id, ty),

        AstNode::InstTarget(ast) => {
            let mut named_params = vec![];
            let mut pos_params = vec![];
            let mut is_pos = true;
            for param in &ast.params {
                let value_id = cx.map_ast_with_parent(AstNode::TypeOrExpr(&param.expr), node_id);
                if let Some(name) = param.name {
                    is_pos = false;
                    named_params.push((param.span, Spanned::new(name.name, name.span), value_id));
                } else {
                    if !is_pos {
                        cx.emit(
                            DiagBuilder2::warning("positional parameters must appear before named")
                                .span(param.span)
                                .add_note(format!(
                                    "assuming this refers to argument #{}",
                                    pos_params.len() + 1
                                )),
                        );
                    }
                    pos_params.push((param.span, value_id));
                }
            }
            let hir = hir::InstTarget {
                id: node_id,
                name: Spanned::new(ast.target.name, ast.target.span),
                span: ast.span,
                pos_params,
                named_params,
            };
            Ok(HirNode::InstTarget(cx.arena().alloc_hir(hir)))
        }
        AstNode::Inst(inst, target_id) => {
            let hir = hir::Inst {
                id: node_id,
                name: Spanned::new(inst.name.name, inst.name.span),
                span: inst.span,
                target: target_id,
                dummy: Default::default(),
            };
            Ok(HirNode::Inst(cx.arena().alloc_hir(hir)))
        }
        AstNode::TypeParam(param, decl) => {
            let hir = hir::TypeParam {
                id: node_id,
                name: Spanned::new(decl.name.name, decl.name.span),
                span: Span::union(param.span, decl.span),
                local: param.local,
                default: decl.ty.as_ref().map(|ty| {
                    let id = cx.map_ast(AstNode::Type(ty));
                    cx.set_parent(id, cx.parent_node_id(node_id).unwrap());
                    id
                }),
            };
            Ok(HirNode::TypeParam(cx.arena().alloc_hir(hir)))
        }
        _ => cx.unimp_msg("lowering of", &ast),
    }
}

fn lower_module<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    ast: &'gcx ast::ModDecl,
) -> Result<HirNode<'gcx>> {
    let mut next_rib = node_id;

    // Allocate parameters.
    let mut params = Vec::new();
    for param in &ast.params {
        match param.kind {
            ast::ParamKind::Type(ref decls) => {
                for decl in decls {
                    let id = cx.map_ast(AstNode::TypeParam(param, decl));
                    cx.set_parent(id, next_rib);
                    next_rib = id;
                    params.push(id);
                }
            }
            ast::ParamKind::Value(ref decls) => {
                for decl in decls {
                    let id = cx.map_ast(AstNode::ValueParam(param, decl));
                    cx.set_parent(id, next_rib);
                    next_rib = id;
                    params.push(id);
                }
            }
        }
    }

    // Allocate ports.
    let mut ports = Vec::new();
    for port in &ast.ports {
        match *port {
            ast::Port::Named { .. } => {
                let id = cx.map_ast(AstNode::Port(port));
                cx.set_parent(id, next_rib);
                next_rib = id;
                ports.push(id);
            }
            _ => return cx.unimp(port),
        }
    }

    // Allocate items.
    let mut insts = Vec::new();
    for item in &ast.items {
        match *item {
            ast::HierarchyItem::Inst(ref inst) => {
                let target_id = cx.map_ast(AstNode::InstTarget(inst));
                cx.set_parent(target_id, next_rib);
                next_rib = target_id;
                trace!(
                    "instantiation target `{}` => {:?}",
                    inst.target.name,
                    target_id
                );
                for inst in &inst.names {
                    let inst_id = cx.map_ast(AstNode::Inst(inst, target_id));
                    trace!("instantiation `{}` => {:?}", inst.name.name, inst_id);
                    cx.set_parent(inst_id, next_rib);
                    next_rib = inst_id;
                    insts.push(inst_id);
                }
            }
            // _ => return cx.unimp_msg("lowering of", item),
            _ => (),
        }
    }

    let hir = hir::Module {
        id: node_id,
        name: Spanned::new(ast.name, ast.name_span),
        span: ast.span,
        ports: cx.arena().alloc_ids(ports),
        params: cx.arena().alloc_ids(params),
        insts: cx.arena().alloc_ids(insts),
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
    cx.set_parent(hir.ty, cx.parent_node_id(node_id).unwrap());
    Ok(HirNode::Port(cx.arena().alloc_hir(hir)))
}

fn lower_type<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    ty: &'gcx ast::Type,
) -> Result<HirNode<'gcx>> {
    let kind = match ty.data {
        ast::VoidType => hir::TypeKind::Builtin(hir::BuiltinType::Void),
        ast::BitType => hir::TypeKind::Builtin(hir::BuiltinType::Bit),
        ast::LogicType => hir::TypeKind::Builtin(hir::BuiltinType::Logic),
        ast::ByteType => hir::TypeKind::Builtin(hir::BuiltinType::Byte),
        ast::ShortIntType => hir::TypeKind::Builtin(hir::BuiltinType::ShortInt),
        ast::IntType => hir::TypeKind::Builtin(hir::BuiltinType::Int),
        ast::LongIntType => hir::TypeKind::Builtin(hir::BuiltinType::LongInt),
        ast::NamedType(name) => hir::TypeKind::Named(Spanned::new(name.name, name.span)),
        _ => return cx.unimp_msg("lowering of", ty),
    };
    let hir = hir::Type {
        id: node_id,
        span: ty.span,
        kind: kind,
    };
    Ok(HirNode::Type(cx.arena().alloc_hir(hir)))
}
