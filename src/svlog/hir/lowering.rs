// Copyright (c) 2016-2019 Fabian Schuiki

//! Lowering of AST nodes to HIR nodes.

use crate::{ast_map::AstNode, crate_prelude::*, hir::HirNode};
use num::BigInt;

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
        AstNode::Type(ty) => lower_type(cx, node_id, ty),
        AstNode::TypeOrExpr(&ast::TypeOrExpr::Type(ref ty)) => lower_type(cx, node_id, ty),
        AstNode::TypeOrExpr(&ast::TypeOrExpr::Expr(ref expr)) => lower_expr(cx, node_id, expr),
        // AstNode::TypeOrExpr(&ast::TypeOrExpr::Type(ref ty))
        //     if cx.lowering_hint(node_id) == Some(Hint::Type) =>
        // {
        //     lower_type(cx, node_id, ty)
        // }
        // AstNode::TypeOrExpr(&ast::TypeOrExpr::Expr(ref expr))
        //     if cx.lowering_hint(node_id) == Some(Hint::Expr) =>
        // {
        //     lower_expr(cx, node_id, expr)
        // }
        AstNode::Expr(expr) => lower_expr(cx, node_id, expr),
        AstNode::InstTarget(ast) => {
            let mut named_params = vec![];
            let mut pos_params = vec![];
            let mut is_pos = true;
            for param in &ast.params {
                let value_id = cx.map_ast_with_parent(AstNode::TypeOrExpr(&param.expr), node_id);
                if let Some(name) = param.name {
                    is_pos = false;
                    named_params.push((
                        param.span,
                        Spanned::new(name.name, name.span),
                        Some(value_id),
                    ));
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
                    pos_params.push((param.span, Some(value_id)));
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
            let mut named_ports = vec![];
            let mut pos_ports = vec![];
            let mut has_wildcard_port = false;
            let mut is_pos = true;
            for port in &inst.conns {
                match port.kind {
                    ast::PortConnKind::Auto => has_wildcard_port = true,
                    ast::PortConnKind::Named(name, ref mode) => {
                        let name = Spanned::new(name.name, name.span);
                        is_pos = false;
                        let value_id = match *mode {
                            ast::PortConnMode::Auto => Some(cx.resolve_upwards_or_error(
                                name,
                                cx.parent_node_id(node_id).unwrap(),
                            )?),
                            ast::PortConnMode::Unconnected => None,
                            ast::PortConnMode::Connected(ref expr) => {
                                Some(cx.map_ast_with_parent(AstNode::Expr(expr), node_id))
                            }
                        };
                        named_ports.push((port.span, name, value_id));
                    }
                    ast::PortConnKind::Positional(ref expr) => {
                        if !is_pos {
                            cx.emit(
                                DiagBuilder2::warning("positional port must appear before named")
                                    .span(port.span)
                                    .add_note(format!(
                                        "assuming this refers to argument #{}",
                                        pos_ports.len() + 1
                                    )),
                            );
                        }
                        let value_id = cx.map_ast_with_parent(AstNode::Expr(expr), node_id);
                        pos_ports.push((port.span, Some(value_id)));
                    }
                }
            }
            let hir = hir::Inst {
                id: node_id,
                name: Spanned::new(inst.name.name, inst.name.span),
                span: inst.span,
                target: target_id,
                named_ports,
                pos_ports,
                has_wildcard_port,
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
                ast::IfStmt {
                    ref cond,
                    ref main_stmt,
                    ref else_stmt,
                    ..
                } => hir::StmtKind::If {
                    cond: cx.map_ast_with_parent(AstNode::Expr(cond), node_id),
                    main_stmt: cx.map_ast_with_parent(AstNode::Stmt(main_stmt), node_id),
                    else_stmt: else_stmt
                        .as_ref()
                        .map(|else_stmt| cx.map_ast_with_parent(AstNode::Stmt(else_stmt), node_id)),
                },
                ast::ExprStmt(ref expr) => {
                    hir::StmtKind::Expr(cx.map_ast_with_parent(AstNode::Expr(expr), node_id))
                }
                ast::ForeverStmt(ref body) => hir::StmtKind::Loop {
                    kind: hir::LoopKind::Forever,
                    body: cx.map_ast_with_parent(AstNode::Stmt(body), node_id),
                },
                ast::RepeatStmt(ref count, ref body) => hir::StmtKind::Loop {
                    kind: hir::LoopKind::Repeat(
                        cx.map_ast_with_parent(AstNode::Expr(count), node_id),
                    ),
                    body: cx.map_ast_with_parent(AstNode::Stmt(body), node_id),
                },
                ast::WhileStmt(ref cond, ref body) => hir::StmtKind::Loop {
                    kind: hir::LoopKind::While(
                        cx.map_ast_with_parent(AstNode::Expr(cond), node_id),
                    ),
                    body: cx.map_ast_with_parent(AstNode::Stmt(body), node_id),
                },
                ast::DoStmt(ref body, ref cond) => hir::StmtKind::Loop {
                    kind: hir::LoopKind::Do(cx.map_ast_with_parent(AstNode::Expr(cond), node_id)),
                    body: cx.map_ast_with_parent(AstNode::Stmt(body), node_id),
                },
                ast::ForStmt(ref init, ref cond, ref step, ref body) => {
                    let init = cx.map_ast_with_parent(AstNode::Stmt(init), node_id);
                    let cond = cx.map_ast_with_parent(AstNode::Expr(cond), init);
                    let step = cx.map_ast_with_parent(AstNode::Expr(step), init);
                    hir::StmtKind::Loop {
                        kind: hir::LoopKind::For(init, cond, step),
                        body: cx.map_ast_with_parent(AstNode::Stmt(body), init),
                    }
                }
                ast::VarDeclStmt(ref decls) => {
                    let mut stmts = vec![];
                    let parent = cx.parent_node_id(node_id).unwrap();
                    let rib = alloc_var_decl(cx, decls, parent, &mut stmts);
                    hir::StmtKind::InlineGroup { stmts, rib }
                }
                ast::NonblockingAssignStmt {
                    ref lhs,
                    ref rhs,
                    ref delay,
                    ..
                } => hir::StmtKind::Assign {
                    lhs: cx.map_ast_with_parent(AstNode::Expr(lhs), node_id),
                    rhs: cx.map_ast_with_parent(AstNode::Expr(rhs), node_id),
                    kind: match *delay {
                        Some(ref dc) => hir::AssignKind::NonblockDelay(
                            cx.map_ast_with_parent(AstNode::Expr(&dc.expr), node_id),
                        ),
                        None => hir::AssignKind::Nonblock,
                    },
                },
                ast::CaseStmt {
                    ref expr,
                    mode: ast::CaseMode::Normal,
                    ref items,
                    ..
                } => {
                    let expr = cx.map_ast_with_parent(AstNode::Expr(expr), node_id);
                    let mut ways = vec![];
                    let mut default = None;
                    for item in items {
                        match *item {
                            ast::CaseItem::Default(ref stmt) => {
                                if default.is_none() {
                                    default =
                                        Some(cx.map_ast_with_parent(AstNode::Stmt(stmt), node_id));
                                } else {
                                    cx.emit(
                                        DiagBuilder2::error("multiple default cases")
                                            .span(stmt.human_span()),
                                    );
                                }
                            }
                            ast::CaseItem::Expr(ref exprs, ref stmt) => ways.push((
                                exprs
                                    .iter()
                                    .map(|expr| {
                                        cx.map_ast_with_parent(AstNode::Expr(expr), node_id)
                                    })
                                    .collect(),
                                cx.map_ast_with_parent(AstNode::Stmt(stmt), node_id),
                            )),
                        }
                    }
                    hir::StmtKind::Case {
                        expr,
                        ways,
                        default,
                    }
                }
                ast::AssertionStmt { .. } => {
                    warn!("ignoring unsupported assertion `{}`", stmt.span.extract());
                    hir::StmtKind::Null
                }
                _ => {
                    error!("{:#?}", stmt);
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
        AstNode::EventExpr(expr) => {
            let mut events = vec![];
            lower_event_expr(cx, expr, node_id, &mut events, &mut vec![])?;
            let hir = hir::EventExpr {
                id: node_id,
                span: expr.span(),
                events,
            };
            Ok(HirNode::EventExpr(cx.arena().alloc_hir(hir)))
        }
        AstNode::GenIf(gen) => {
            let cond = cx.map_ast_with_parent(AstNode::Expr(&gen.cond), node_id);
            let main_body = lower_module_block(cx, node_id, &gen.main_block.items)?;
            let else_body = match gen.else_block {
                Some(ref else_block) => Some(lower_module_block(cx, node_id, &else_block.items)?),
                None => None,
            };
            let hir = hir::Gen {
                id: node_id,
                span: gen.span(),
                kind: hir::GenKind::If {
                    cond,
                    main_body,
                    else_body,
                },
            };
            Ok(HirNode::Gen(cx.arena().alloc_hir(hir)))
        }
        AstNode::GenFor(gen) => {
            let init = alloc_genvar_init(cx, &gen.init, node_id)?;
            let rib = *init.last().unwrap();
            let cond = cx.map_ast_with_parent(AstNode::Expr(&gen.cond), rib);
            let step = cx.map_ast_with_parent(AstNode::Expr(&gen.step), rib);
            let body = lower_module_block(cx, rib, &gen.block.items)?;
            let hir = hir::Gen {
                id: node_id,
                span: gen.span(),
                kind: hir::GenKind::For {
                    init,
                    cond,
                    step,
                    body,
                },
            };
            Ok(HirNode::Gen(cx.arena().alloc_hir(hir)))
        }
        AstNode::GenvarDecl(decl) => {
            let hir = hir::GenvarDecl {
                id: node_id,
                span: decl.span(),
                name: Spanned::new(decl.name, decl.name_span),
                init: decl
                    .init
                    .as_ref()
                    .map(|init| cx.map_ast_with_parent(AstNode::Expr(init), node_id)),
            };
            Ok(HirNode::GenvarDecl(cx.arena().alloc_hir(hir)))
        }
        AstNode::Typedef(def) => {
            let hir = hir::Typedef {
                id: node_id,
                span: def.span(),
                name: Spanned::new(def.name.name, def.name.span),
                ty: cx.map_ast_with_parent(
                    AstNode::Type(&def.ty),
                    cx.parent_node_id(node_id).unwrap(),
                ),
            };
            Ok(HirNode::Typedef(cx.arena().alloc_hir(hir)))
        }
        AstNode::ContAssign(_, lhs, rhs) => {
            let hir = hir::Assign {
                id: node_id,
                span: Span::union(lhs.span(), rhs.span()),
                lhs: cx.map_ast_with_parent(AstNode::Expr(lhs), node_id),
                rhs: cx.map_ast_with_parent(AstNode::Expr(rhs), node_id),
            };
            Ok(HirNode::Assign(cx.arena().alloc_hir(hir)))
        }
        AstNode::StructMember(name, decl, ty) => {
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
        AstNode::Package(p) => lower_package(cx, node_id, p),
        AstNode::EnumVariant(var, decl, index) => {
            let hir = hir::EnumVariant {
                id: node_id,
                name: Spanned::new(var.name.name, var.name.span),
                span: var.name.span,
                enum_id: decl,
                index,
                value: var
                    .value
                    .as_ref()
                    .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), decl)),
            };
            Ok(HirNode::EnumVariant(cx.arena().alloc_hir(hir)))
        }
        AstNode::Import(import) => unreachable!("import should never be lowered: {:#?}", import),
        _ => {
            error!("{:#?}", ast);
            cx.unimp_msg("lowering of", &ast)
        }
    }
}

/// Lower a module to HIR.
///
/// This allocates node IDs to everything in the module and registers AST nodes
/// for each ID.
fn lower_module<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    ast: &'gcx ast::ModDecl,
) -> Result<HirNode<'gcx>> {
    let mut next_rib = node_id;

    // Allocate parameters.
    let mut params = Vec::new();
    for param in &ast.params {
        next_rib = alloc_param_decl(cx, param, next_rib, &mut params);
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
    let block = lower_module_block(cx, next_rib, &ast.items)?;

    let hir = hir::Module {
        id: node_id,
        name: Spanned::new(ast.name, ast.name_span),
        span: ast.span,
        ports: cx.arena().alloc_ids(ports),
        params: cx.arena().alloc_ids(params),
        block,
    };
    Ok(HirNode::Module(cx.arena().alloc_hir(hir)))
}

fn lower_module_block<'gcx>(
    cx: &impl Context<'gcx>,
    parent_rib: NodeId,
    items: impl IntoIterator<Item = &'gcx ast::HierarchyItem>,
) -> Result<hir::ModuleBlock> {
    let mut next_rib = parent_rib;
    let mut insts = Vec::new();
    let mut decls = Vec::new();
    let mut procs = Vec::new();
    let mut gens = Vec::new();
    let mut params = Vec::new();
    let mut assigns = Vec::new();
    for item in items {
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
                next_rib = alloc_var_decl(cx, decl, next_rib, &mut decls);
            }
            ast::HierarchyItem::Procedure(ref prok) => {
                let id = cx.map_ast_with_parent(AstNode::Proc(prok), next_rib);
                next_rib = id;
                procs.push(id);
            }
            ast::HierarchyItem::GenerateIf(ref gen) => {
                let id = cx.map_ast_with_parent(AstNode::GenIf(gen), next_rib);
                next_rib = id;
                gens.push(id);
            }
            ast::HierarchyItem::GenerateFor(ref gen) => {
                let id = cx.map_ast_with_parent(AstNode::GenFor(gen), next_rib);
                next_rib = id;
                gens.push(id);
            }
            ast::HierarchyItem::ParamDecl(ref param) => {
                next_rib = alloc_param_decl(cx, param, next_rib, &mut params);
            }
            ast::HierarchyItem::Typedef(ref def) => {
                let id = cx.map_ast_with_parent(AstNode::Typedef(def), next_rib);
                next_rib = id;
            }
            ast::HierarchyItem::ContAssign(ref assign) => {
                for &(ref lhs, ref rhs) in &assign.assignments {
                    let id =
                        cx.map_ast_with_parent(AstNode::ContAssign(assign, lhs, rhs), next_rib);
                    next_rib = id;
                    assigns.push(id);
                }
            }
            ast::HierarchyItem::ImportDecl(ref decl) => {
                for item in &decl.items {
                    let id = cx.map_ast_with_parent(AstNode::Import(item), next_rib);
                    next_rib = id;
                }
            }
            // _ => return cx.unimp_msg("lowering of", item),
            _ => warn!("skipping unsupported {:?}", item),
        }
    }
    Ok(hir::ModuleBlock {
        insts,
        decls,
        procs,
        gens,
        params,
        assigns,
    })
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
    let mut kind = match ty.data {
        ast::ImplicitType => hir::TypeKind::Implicit,
        ast::VoidType => hir::TypeKind::Builtin(hir::BuiltinType::Void),
        ast::BitType => hir::TypeKind::Builtin(hir::BuiltinType::Bit),
        ast::LogicType => hir::TypeKind::Builtin(hir::BuiltinType::Logic),
        ast::ByteType => hir::TypeKind::Builtin(hir::BuiltinType::Byte),
        ast::ShortIntType => hir::TypeKind::Builtin(hir::BuiltinType::ShortInt),
        ast::IntType => hir::TypeKind::Builtin(hir::BuiltinType::Int),
        ast::IntegerType => hir::TypeKind::Builtin(hir::BuiltinType::Integer),
        ast::LongIntType => hir::TypeKind::Builtin(hir::BuiltinType::LongInt),
        ast::NamedType(name) => hir::TypeKind::Named(Spanned::new(name.name, name.span)),
        ast::StructType { ref members, .. } => {
            let mut fields = vec![];
            let mut next_rib = node_id;
            for member in members {
                next_rib = alloc_struct_member(cx, member, next_rib, &mut fields);
            }
            hir::TypeKind::Struct(fields)
        }
        ast::ScopedType {
            ref ty,
            member: false,
            name,
        } => hir::TypeKind::Scope(
            cx.map_ast_with_parent(AstNode::Type(ty.as_ref()), node_id),
            Spanned::new(name.name, name.span),
        ),
        ast::EnumType(ref repr_ty, ref names) => {
            let mut next_rib = node_id;
            let ty = match repr_ty {
                Some(ref ty) => {
                    next_rib = cx.map_ast_with_parent(AstNode::Type(ty), next_rib);
                    Some(next_rib)
                }
                None => None,
            };
            let mut variants = vec![];
            for (index, name) in names.iter().enumerate() {
                next_rib =
                    cx.map_ast_with_parent(AstNode::EnumVariant(name, node_id, index), next_rib);
                variants.push((Spanned::new(name.name.name, name.name.span), next_rib));
            }
            hir::TypeKind::Enum(variants, ty)
        }
        _ => {
            error!("{:#?}", ty);
            return cx.unimp_msg("lowering of", ty);
        }
    };
    for dim in ty.dims.iter().rev() {
        match *dim {
            ast::TypeDim::Range(ref lhs, ref rhs) => {
                kind = hir::TypeKind::PackedArray(
                    Box::new(kind),
                    cx.map_ast_with_parent(AstNode::Expr(lhs), node_id),
                    cx.map_ast_with_parent(AstNode::Expr(rhs), node_id),
                );
            }
            _ => {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "{} is not a valid packed dimension",
                        dim.desc_full()
                    ))
                    .span(ty.human_span())
                    .add_note("packed array dimensions can only be given as range, e.g. `[31:0]`"),
                );
                return Err(());
            }
        }
    }
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
    use crate::syntax::token::{Lit, Op};
    let parent = cx.parent_node_id(node_id).unwrap();
    let kind = match expr.data {
        ast::LiteralExpr(Lit::Number(v, None)) => match v.as_str().parse() {
            Ok(v) => hir::ExprKind::IntConst(32, v),
            Err(e) => {
                cx.emit(
                    DiagBuilder2::error(format!("`{}` is not a valid integer literal", v))
                        .span(expr.span)
                        .add_note(format!("{}", e)),
                );
                return Err(());
            }
        },
        ast::LiteralExpr(Lit::UnbasedUnsized(c)) => hir::ExprKind::UnsizedConst(c),
        ast::LiteralExpr(Lit::BasedInteger(maybe_size, _signed, base, value)) => {
            let parsed = BigInt::parse_bytes(
                value
                    .as_str()
                    .chars()
                    .map(|c| match c {
                        'x' | 'X' | 'z' | 'Z' | '?' | '-' => '0',
                        c => c,
                    })
                    .collect::<String>()
                    .as_bytes(),
                match base {
                    'h' => 16,
                    'd' => 10,
                    'o' => 8,
                    'b' => 2,
                    _ => {
                        cx.emit(
                            DiagBuilder2::error(format!("`{}` is not a valid integer base", base))
                                .span(expr.span)
                                .add_note("valid bases are `b`, `o`, `d`, and `h`"),
                        );
                        return Err(());
                    }
                },
            );
            let parsed = match parsed {
                Some(parsed) => parsed,
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!("`{}` is not a valid integer literal", value))
                            .span(expr.span),
                    );
                    return Err(());
                }
            };
            let size_needed = parsed.bits();
            let size = match maybe_size {
                Some(size) => match size.as_str().parse() {
                    Ok(s) => s,
                    Err(e) => {
                        cx.emit(
                            DiagBuilder2::error(format!("`{}` is not a valid integer size", size))
                                .span(expr.span)
                                .add_note(format!("{}", e)),
                        );
                        return Err(());
                    }
                },
                None => size_needed,
            };
            if size_needed > size {
                cx.emit(DiagBuilder2::warning(format!(
                    "`{}` is too large",
                    value,
                )).span(expr.span).add_note(format!("constant is {} bits wide, but the value `{}{}` needs {} bits to not be truncated", size, base, value, size_needed)));
            }
            hir::ExprKind::IntConst(size, parsed)
        }
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
        ast::UnaryExpr {
            op,
            expr: ref arg,
            postfix,
        } => hir::ExprKind::Unary(
            match op {
                Op::Add if !postfix => hir::UnaryOp::Pos,
                Op::Sub if !postfix => hir::UnaryOp::Neg,
                Op::BitNot if !postfix => hir::UnaryOp::BitNot,
                Op::LogicNot if !postfix => hir::UnaryOp::LogicNot,
                Op::Inc if !postfix => hir::UnaryOp::PreInc,
                Op::Dec if !postfix => hir::UnaryOp::PreDec,
                Op::Inc if postfix => hir::UnaryOp::PostInc,
                Op::Dec if postfix => hir::UnaryOp::PostDec,
                Op::BitAnd if !postfix => hir::UnaryOp::RedAnd,
                Op::BitNand if !postfix => hir::UnaryOp::RedNand,
                Op::BitOr if !postfix => hir::UnaryOp::RedOr,
                Op::BitNor if !postfix => hir::UnaryOp::RedNor,
                Op::BitXor if !postfix => hir::UnaryOp::RedXor,
                Op::BitNxor if !postfix => hir::UnaryOp::RedXnor,
                Op::BitXnor if !postfix => hir::UnaryOp::RedXnor,
                _ => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "`{}` is not a valid {} operator",
                            op,
                            match postfix {
                                true => "postfix",
                                false => "prefix",
                            }
                        ))
                        .span(expr.span()),
                    );
                    return Err(());
                }
            },
            cx.map_ast_with_parent(AstNode::Expr(arg), parent),
        ),
        ast::BinaryExpr {
            op,
            ref lhs,
            ref rhs,
        } => hir::ExprKind::Binary(
            match op {
                Op::Add => hir::BinaryOp::Add,
                Op::Sub => hir::BinaryOp::Sub,
                Op::Mul => hir::BinaryOp::Mul,
                Op::Div => hir::BinaryOp::Div,
                Op::Mod => hir::BinaryOp::Mod,
                Op::Pow => hir::BinaryOp::Pow,
                Op::LogicEq => hir::BinaryOp::Eq,
                Op::LogicNeq => hir::BinaryOp::Neq,
                Op::Lt => hir::BinaryOp::Lt,
                Op::Leq => hir::BinaryOp::Leq,
                Op::Gt => hir::BinaryOp::Gt,
                Op::Geq => hir::BinaryOp::Geq,
                Op::LogicAnd => hir::BinaryOp::LogicAnd,
                Op::LogicOr => hir::BinaryOp::LogicOr,
                Op::BitAnd => hir::BinaryOp::BitAnd,
                Op::BitNand => hir::BinaryOp::BitNand,
                Op::BitOr => hir::BinaryOp::BitOr,
                Op::BitNor => hir::BinaryOp::BitNor,
                Op::BitXor => hir::BinaryOp::BitXor,
                Op::BitXnor => hir::BinaryOp::BitXnor,
                Op::BitNxor => hir::BinaryOp::BitXnor,
                Op::LogicShL => hir::BinaryOp::LogicShL,
                Op::LogicShR => hir::BinaryOp::LogicShR,
                Op::ArithShL => hir::BinaryOp::ArithShL,
                Op::ArithShR => hir::BinaryOp::ArithShR,
                _ => {
                    cx.emit(
                        DiagBuilder2::error(format!("`{}` is not a valid binary operator", op,))
                            .span(expr.span()),
                    );
                    return Err(());
                }
            },
            cx.map_ast_with_parent(AstNode::Expr(lhs), parent),
            cx.map_ast_with_parent(AstNode::Expr(rhs), parent),
        ),
        ast::MemberExpr { ref expr, name } => hir::ExprKind::Field(
            cx.map_ast_with_parent(AstNode::Expr(expr), parent),
            Spanned::new(name.name, name.span),
        ),
        ast::IndexExpr {
            ref indexee,
            ref index,
        } => {
            let indexee = cx.map_ast_with_parent(AstNode::Expr(indexee), parent);
            let mode = match index.data {
                ast::RangeExpr {
                    mode,
                    ref lhs,
                    ref rhs,
                } => hir::IndexMode::Many(
                    mode,
                    cx.map_ast_with_parent(AstNode::Expr(lhs), parent),
                    cx.map_ast_with_parent(AstNode::Expr(rhs), parent),
                ),
                _ => hir::IndexMode::One(cx.map_ast_with_parent(AstNode::Expr(index), parent)),
            };
            hir::ExprKind::Index(indexee, mode)
        }
        ast::CallExpr(ref callee, ref args) => match callee.data {
            ast::SysIdentExpr(ident) => {
                let map_unary = || {
                    Ok(match args.as_slice() {
                        [ast::CallArg {
                            expr: Some(ref arg),
                            ..
                        }] => cx.map_ast_with_parent(AstNode::Expr(arg), parent),
                        _ => {
                            cx.emit(
                                DiagBuilder2::error(format!("`{}` takes one argument", ident.name))
                                    .span(expr.human_span()),
                            );
                            return Err(());
                        }
                    })
                };
                hir::ExprKind::Builtin(match &*ident.name.as_str() {
                    "clog2" => hir::BuiltinCall::Clog2(map_unary()?),
                    "bits" => hir::BuiltinCall::Bits(map_unary()?),
                    "signed" => hir::BuiltinCall::Signed(map_unary()?),
                    "unsigned" => hir::BuiltinCall::Unsigned(map_unary()?),
                    _ => {
                        cx.emit(
                            DiagBuilder2::error(format!("`${}` unknown", ident.name))
                                .span(expr.human_span()),
                        );
                        return Err(());
                    }
                })
            }
            _ => {
                error!("{:#?}", callee);
                return cx.unimp_msg("lowering of call to", callee.as_ref());
            }
        },
        ast::TernaryExpr {
            ref cond,
            ref true_expr,
            ref false_expr,
        } => hir::ExprKind::Ternary(
            cx.map_ast_with_parent(AstNode::Expr(cond), parent),
            cx.map_ast_with_parent(AstNode::Expr(true_expr), parent),
            cx.map_ast_with_parent(AstNode::Expr(false_expr), parent),
        ),
        ast::ScopeExpr(ref expr, name) => hir::ExprKind::Scope(
            cx.map_ast_with_parent(AstNode::Expr(expr.as_ref()), node_id),
            Spanned::new(name.name, name.span),
        ),
        ast::PatternExpr(ref fields) if fields.is_empty() => hir::ExprKind::EmptyPattern,
        ast::PatternExpr(ref fields) => {
            let deciding_span = fields[0].span;
            match fields[0].data {
                ast::PatternFieldData::Expr(_) => {
                    let mut mapping = vec![];
                    for field in fields {
                        mapping.push(match field.data {
                            ast::PatternFieldData::Expr(ref expr) => {
                                cx.map_ast_with_parent(AstNode::Expr(expr.as_ref()), node_id)
                            }
                            _ => {
                                cx.emit(
                                    DiagBuilder2::error(format!(
                                        "`{}` not a positional pattern",
                                        field.span.extract()
                                    ))
                                    .span(field.span)
                                    .add_note(
                                        "required because first field was a positional pattern,
                                             and all fields must be the same:",
                                    )
                                    .span(deciding_span),
                                );
                                continue;
                            }
                        });
                    }
                    hir::ExprKind::PositionalPattern(mapping)
                }
                ast::PatternFieldData::Repeat(ref count, ref exprs) => {
                    for field in &fields[1..] {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "`{}` after repeat pattern",
                                field.span.extract()
                            ))
                            .span(field.span)
                            .add_note("repeat patterns must have the form `'{<expr>{...}}`"),
                        );
                    }
                    hir::ExprKind::RepeatPattern(
                        cx.map_ast_with_parent(AstNode::Expr(count), node_id),
                        exprs
                            .iter()
                            .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), node_id))
                            .collect(),
                    )
                }
                ast::PatternFieldData::Type(..)
                | ast::PatternFieldData::Member(..)
                | ast::PatternFieldData::Default(..) => {
                    let mut mapping = vec![];
                    for field in fields {
                        mapping.push(match field.data {
                            ast::PatternFieldData::Type(ref ty, ref expr) => (
                                hir::PatternMapping::Type(
                                    cx.map_ast_with_parent(AstNode::Type(ty), node_id),
                                ),
                                cx.map_ast_with_parent(AstNode::Expr(expr.as_ref()), node_id),
                            ),
                            ast::PatternFieldData::Member(ref member, ref expr) => (
                                hir::PatternMapping::Member(
                                    cx.map_ast_with_parent(AstNode::Expr(member.as_ref()), node_id),
                                ),
                                cx.map_ast_with_parent(AstNode::Expr(expr.as_ref()), node_id),
                            ),
                            ast::PatternFieldData::Default(ref expr) => (
                                hir::PatternMapping::Default,
                                cx.map_ast_with_parent(AstNode::Expr(expr.as_ref()), node_id),
                            ),
                            _ => {
                                cx.emit(
                                    DiagBuilder2::error(format!(
                                        "`{}` not a named pattern",
                                        field.span.extract()
                                    ))
                                    .span(field.span)
                                    .add_note(
                                        "required because first field was a named pattern,
                                             and all fields must be the same:",
                                    )
                                    .span(deciding_span),
                                );
                                continue;
                            }
                        });
                    }
                    hir::ExprKind::NamedPattern(mapping)
                }
            }
        }
        ast::ConcatExpr {
            ref repeat,
            ref exprs,
        } => hir::ExprKind::Concat(
            repeat
                .as_ref()
                .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), parent)),
            exprs
                .iter()
                .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), parent))
                .collect(),
        ),
        ast::CastExpr(ref ty, ref expr) => hir::ExprKind::Cast(
            cx.map_ast_with_parent(AstNode::Type(ty), parent),
            cx.map_ast_with_parent(AstNode::Expr(expr), parent),
        ),
        _ => {
            error!("{:#?}", expr);
            return cx.unimp_msg("lowering of", expr);
        }
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

fn lower_event_expr<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &'gcx ast::EventExpr,
    parent_id: NodeId,
    into: &mut Vec<hir::Event>,
    cond_stack: &mut Vec<NodeId>,
) -> Result<()> {
    match *expr {
        ast::EventExpr::Edge {
            span,
            edge,
            ref value,
        } => {
            into.push(hir::Event {
                span,
                edge,
                expr: cx.map_ast_with_parent(AstNode::Expr(value), parent_id),
                iff: cond_stack.clone(),
            });
        }
        ast::EventExpr::Iff {
            ref expr, ref cond, ..
        } => {
            cond_stack.push(cx.map_ast_with_parent(AstNode::Expr(cond), parent_id));
            lower_event_expr(cx, expr, parent_id, into, cond_stack)?;
            cond_stack.pop().unwrap();
        }
        ast::EventExpr::Or {
            ref lhs, ref rhs, ..
        } => {
            lower_event_expr(cx, lhs, parent_id, into, cond_stack)?;
            lower_event_expr(cx, rhs, parent_id, into, cond_stack)?;
        }
    };
    Ok(())
}

/// Lower a list of genvar declarations.
fn alloc_genvar_init<'gcx>(
    cx: &impl Context<'gcx>,
    stmt: &'gcx ast::Stmt,
    mut parent_id: NodeId,
) -> Result<Vec<NodeId>> {
    let mut ids = vec![];
    match stmt.data {
        ast::GenvarDeclStmt(ref decls) => {
            for decl in decls {
                let id = cx.map_ast_with_parent(AstNode::GenvarDecl(decl), parent_id);
                ids.push(id);
                parent_id = id;
            }
        }
        _ => {
            cx.emit(
                DiagBuilder2::error(format!(
                    "{} is not a valid genvar initialization",
                    stmt.desc_full()
                ))
                .span(stmt.human_span()),
            );
            return Err(());
        }
    }
    Ok(ids)
}

/// Allocate node IDs for a parameter declaration.
fn alloc_param_decl<'gcx>(
    cx: &impl Context<'gcx>,
    param: &'gcx ast::ParamDecl,
    mut next_rib: NodeId,
    into: &mut Vec<NodeId>,
) -> NodeId {
    match param.kind {
        ast::ParamKind::Type(ref decls) => {
            for decl in decls {
                let id = cx.map_ast(AstNode::TypeParam(param, decl));
                cx.set_parent(id, next_rib);
                next_rib = id;
                into.push(id);
            }
        }
        ast::ParamKind::Value(ref decls) => {
            for decl in decls {
                let id = cx.map_ast(AstNode::ValueParam(param, decl));
                cx.set_parent(id, next_rib);
                next_rib = id;
                into.push(id);
            }
        }
    }
    next_rib
}

/// Allocate node IDs for a variable declaration.
fn alloc_var_decl<'gcx>(
    cx: &impl Context<'gcx>,
    decl: &'gcx ast::VarDecl,
    mut next_rib: NodeId,
    into: &mut Vec<NodeId>,
) -> NodeId {
    let type_id = cx.map_ast_with_parent(AstNode::Type(&decl.ty), next_rib);
    next_rib = type_id;
    for name in &decl.names {
        let decl_id = cx.map_ast_with_parent(AstNode::VarDecl(name, decl, type_id), next_rib);
        next_rib = decl_id;
        into.push(decl_id);
    }
    next_rib
}

/// Allocate node IDs for a struct member.
fn alloc_struct_member<'gcx>(
    cx: &impl Context<'gcx>,
    member: &'gcx ast::StructMember,
    mut next_rib: NodeId,
    into: &mut Vec<NodeId>,
) -> NodeId {
    let type_id = cx.map_ast_with_parent(AstNode::Type(&member.ty), next_rib);
    next_rib = type_id;
    for name in &member.names {
        let member_id =
            cx.map_ast_with_parent(AstNode::StructMember(name, member, type_id), next_rib);
        next_rib = member_id;
        into.push(member_id);
    }
    next_rib
}

/// Lower a package to HIR.
///
/// This allocates node IDs to everything in the package and registers AST nodes
/// for each ID.
fn lower_package<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    ast: &'gcx ast::PackageDecl,
) -> Result<HirNode<'gcx>> {
    let mut next_rib = node_id;
    let mut names = Vec::new();
    let mut decls = Vec::new();
    let mut params = Vec::new();
    for item in &ast.items {
        match *item {
            ast::HierarchyItem::VarDecl(ref decl) => {
                next_rib = alloc_var_decl(cx, decl, next_rib, &mut decls);
            }
            ast::HierarchyItem::ParamDecl(ref param) => {
                next_rib = alloc_param_decl(cx, param, next_rib, &mut params);
            }
            ast::HierarchyItem::Typedef(ref def) => {
                next_rib = cx.map_ast_with_parent(AstNode::Typedef(def), next_rib);
                names.push((Spanned::new(def.name.name, def.name.span), next_rib));
            }
            ast::HierarchyItem::SubroutineDecl(ref decl) => warn!(
                "ignoring unsupported subroutine `{}`",
                decl.prototype.name.name
            ),
            _ => {
                cx.emit(
                    DiagBuilder2::error(format!("{} cannot appear in a package", item.desc_full()))
                        .span(item.human_span()),
                );
                return Err(());
            }
        }
    }

    let hir = hir::Package {
        id: node_id,
        name: Spanned::new(ast.name, ast.name_span),
        span: ast.span,
        names,
        decls,
        params,
        last_rib: next_rib,
    };
    Ok(HirNode::Package(cx.arena().alloc_hir(hir)))
}
