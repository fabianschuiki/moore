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
        AstNode::TypeOrExpr(&ast::TypeOrExpr::Expr(ref expr))
            if cx.lowering_hint(node_id) == Some(Hint::Expr) =>
        {
            lower_expr(cx, node_id, expr)
        }
        AstNode::Expr(expr) => lower_expr(cx, node_id, expr),
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
                    cx.map_ast_with_parent(AstNode::Type(ty), cx.parent_node_id(node_id).unwrap())
                }),
            };
            Ok(HirNode::TypeParam(cx.arena().alloc_hir(hir)))
        }
        AstNode::ValueParam(param, decl) => {
            let hir = hir::ValueParam {
                id: node_id,
                name: Spanned::new(decl.name.name, decl.name.span),
                span: Span::union(param.span, decl.span),
                local: param.local,
                ty: cx.map_ast_with_parent(
                    AstNode::Type(&decl.ty),
                    cx.parent_node_id(node_id).unwrap(),
                ),
                default: decl.expr.as_ref().map(|expr| {
                    cx.map_ast_with_parent(AstNode::Expr(expr), cx.parent_node_id(node_id).unwrap())
                }),
            };
            Ok(HirNode::ValueParam(cx.arena().alloc_hir(hir)))
        }
        AstNode::VarDecl(name, decl, ty) => {
            let hir = hir::VarDecl {
                id: node_id,
                name: Spanned::new(name.name, name.name_span),
                span: Span::union(name.span, decl.span),
                ty: ty,
                init: name
                    .init
                    .as_ref()
                    .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), ty)),
            };
            Ok(HirNode::VarDecl(cx.arena().alloc_hir(hir)))
        }
        AstNode::Proc(prok) => {
            let hir = hir::Proc {
                id: node_id,
                span: prok.span,
                kind: prok.kind,
                stmt: cx.map_ast_with_parent(AstNode::Stmt(&prok.stmt), node_id),
            };
            Ok(HirNode::Proc(cx.arena().alloc_hir(hir)))
        }
        AstNode::Stmt(stmt) => {
            let kind = match stmt.data {
                ast::NullStmt => hir::StmtKind::Null,
                ast::SequentialBlock(ref stmts) => {
                    let mut next_rib = node_id;
                    hir::StmtKind::Block(
                        stmts
                            .iter()
                            .map(|stmt| {
                                let id = cx.map_ast_with_parent(AstNode::Stmt(stmt), next_rib);
                                next_rib = id;
                                id
                            })
                            .collect(),
                    )
                }
                ast::BlockingAssignStmt {
                    ref lhs,
                    ref rhs,
                    op,
                } => hir::StmtKind::Assign {
                    lhs: cx.map_ast_with_parent(AstNode::Expr(lhs), node_id),
                    rhs: cx.map_ast_with_parent(AstNode::Expr(rhs), node_id),
                    kind: hir::AssignKind::Block(op),
                },
                ast::TimedStmt(ref control, ref inner_stmt) => {
                    let control = match *control {
                        ast::TimingControl::Delay(ref dc) => hir::TimingControl::Delay(
                            cx.map_ast_with_parent(AstNode::Expr(&dc.expr), node_id),
                        ),
                        ast::TimingControl::Event(ref ec) => match ec.data {
                            ast::EventControlData::Implicit => hir::TimingControl::ImplicitEvent,
                            ast::EventControlData::Expr(ref expr) => {
                                hir::TimingControl::ExplicitEvent(
                                    cx.map_ast_with_parent(AstNode::EventExpr(expr), node_id),
                                )
                            }
                        },
                        _ => {
                            debug!("{:#?}", stmt);
                            return cx.unimp_msg("lowering of timing control", stmt);
                        }
                    };
                    hir::StmtKind::Timed {
                        control,
                        stmt: cx.map_ast_with_parent(AstNode::Stmt(inner_stmt), node_id),
                    }
                }
                _ => {
                    debug!("{:#?}", stmt);
                    return cx.unimp_msg("lowering of", stmt);
                }
            };
            let hir = hir::Stmt {
                id: node_id,
                label: stmt.label.map(|n| Spanned::new(n, stmt.span)), // this is horrible...
                span: stmt.span,
                kind: kind,
            };
            Ok(HirNode::Stmt(cx.arena().alloc_hir(hir)))
        }
        _ => {
            debug!("{:#?}", ast);
            cx.unimp_msg("lowering of", &ast)
        }
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
    let mut decls = Vec::new();
    let mut procs = Vec::new();
    for item in &ast.items {
        match *item {
            ast::HierarchyItem::Inst(ref inst) => {
                let target_id = cx.map_ast_with_parent(AstNode::InstTarget(inst), next_rib);
                next_rib = target_id;
                trace!(
                    "instantiation target `{}` => {:?}",
                    inst.target.name,
                    target_id
                );
                for inst in &inst.names {
                    let inst_id = cx.map_ast_with_parent(AstNode::Inst(inst, target_id), next_rib);
                    trace!("instantiation `{}` => {:?}", inst.name.name, inst_id);
                    next_rib = inst_id;
                    insts.push(inst_id);
                }
            }
            ast::HierarchyItem::VarDecl(ref decl) => {
                let type_id = cx.map_ast_with_parent(AstNode::Type(&decl.ty), next_rib);
                next_rib = type_id;
                for name in &decl.names {
                    let decl_id =
                        cx.map_ast_with_parent(AstNode::VarDecl(name, decl, type_id), next_rib);
                    next_rib = decl_id;
                    decls.push(decl_id);
                }
            }
            ast::HierarchyItem::Procedure(ref prok) => {
                let id = cx.map_ast_with_parent(AstNode::Proc(prok), next_rib);
                next_rib = id;
                procs.push(id);
            }
            // _ => return cx.unimp_msg("lowering of", item),
            _ => warn!("skipping unsupported {:?}", item),
        }
    }

    let hir = hir::Module {
        id: node_id,
        name: Spanned::new(ast.name, ast.name_span),
        span: ast.span,
        ports: cx.arena().alloc_ids(ports),
        params: cx.arena().alloc_ids(params),
        insts: cx.arena().alloc_ids(insts),
        decls: cx.arena().alloc_ids(decls),
        procs: cx.arena().alloc_ids(procs),
    };
    Ok(HirNode::Module(cx.arena().alloc_hir(hir)))
}

fn lower_port<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    ast: &'gcx ast::Port,
) -> Result<HirNode<'gcx>> {
    let parent = cx.parent_node_id(node_id).unwrap();
    let hir = match *ast {
        ast::Port::Named {
            span,
            name,
            dir,
            ref ty,
            ref expr,
            ..
        } => hir::Port {
            id: node_id,
            name: Spanned::new(name.name, name.span),
            span: span,
            dir: dir.expect("port missing direction"),
            ty: cx.map_ast_with_parent(AstNode::Type(ty), parent),
            default: expr
                .as_ref()
                .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), parent)),
        },
        _ => return cx.unimp(ast),
    };
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

fn lower_expr<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    expr: &'gcx ast::Expr,
) -> Result<HirNode<'gcx>> {
    use crate::syntax::token::Lit;
    let kind = match expr.data {
        ast::LiteralExpr(Lit::Number(v, None)) => match v.as_str().parse() {
            Ok(v) => hir::ExprKind::IntConst(v),
            Err(e) => {
                cx.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid integer literal", v))
                        .span(expr.span)
                        .add_note(format!("{}", e)),
                );
                return Err(());
            }
        },
        ast::LiteralExpr(Lit::Time(int, frac, unit)) => {
            use syntax::token::TimeUnit;
            let mut value = parse_fixed_point_number(cx, expr.span, int, frac)?;
            let magnitude = match unit {
                TimeUnit::Second => 0,
                TimeUnit::MilliSecond => 1,
                TimeUnit::MicroSecond => 2,
                TimeUnit::NanoSecond => 3,
                TimeUnit::PicoSecond => 4,
                TimeUnit::FemtoSecond => 5,
            };
            for _ in 0..magnitude {
                value = value / num::BigInt::from(1000);
            }
            hir::ExprKind::TimeConst(value)
        }
        ast::IdentExpr(ident) => hir::ExprKind::Ident(Spanned::new(ident.name, ident.span)),
        _ => return cx.unimp_msg("lowering of", expr),
    };
    let hir = hir::Expr {
        id: node_id,
        span: expr.span,
        kind: kind,
    };
    Ok(HirNode::Expr(cx.arena().alloc_hir(hir)))
}

/// Parse a fixed point number into a [`BigRational`].
///
/// The fractional part of the number is optional, such that this function may
/// also be used to parse integers into a ratio.
fn parse_fixed_point_number<'gcx>(
    cx: &impl Context<'gcx>,
    span: Span,
    int: Name,
    frac: Option<Name>,
) -> Result<num::BigRational> {
    let mut num_digits = int.to_string();
    let mut denom_digits = String::from("1");
    if let Some(frac) = frac {
        let s = frac.to_string();
        num_digits.push_str(&s);
        denom_digits.extend(s.chars().map(|_| '0'));
    }
    match (num_digits.parse(), denom_digits.parse()) {
        (Ok(a), Ok(b)) => Ok((a, b).into()),
        (Err(e), _) | (_, Err(e)) => {
            let value = match frac {
                Some(frac) => format!("{}.{}", int, frac),
                None => format!("{}", int),
            };
            cx.emit(
                DiagBuilder2::error(format!("`{}` is not a number literal", value))
                    .span(span)
                    .add_note(format!("{}", e)),
            );
            Err(())
        }
    }
}
