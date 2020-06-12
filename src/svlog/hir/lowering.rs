// Copyright (c) 2016-2020 Fabian Schuiki

//! Lowering of AST nodes to HIR nodes.

use crate::crate_prelude::*;
use crate::{ast_map::AstNode, hir::HirNode};
use bit_vec::BitVec;
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
    if let Some(hir) = cx.get_interned_hir(node_id) {
        return Ok(hir);
    }
    let ast = cx.ast_of(node_id)?;

    #[allow(unreachable_patterns)]
    match ast {
        AstNode::Module(x) => cx.hir_of_module(x).map(HirNode::Module),
        AstNode::Interface(x) => cx.hir_of_interface(x).map(HirNode::Interface),
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
                ast,
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
                match port.data {
                    ast::PortConnData::Auto => has_wildcard_port = true,
                    ast::PortConnData::Named(name, ref mode) => {
                        is_pos = false;
                        let value_id = match *mode {
                            ast::PortConnMode::Auto => {
                                let expr = cx.arena().alloc_ast_expr(ast::Expr::new(
                                    name.span,
                                    ast::IdentExpr(name),
                                ));
                                expr.link_attach(port, port.order());
                                Some(cx.map_ast_with_parent(AstNode::Expr(expr), node_id))
                            }
                            ast::PortConnMode::Unconnected => None,
                            ast::PortConnMode::Connected(ref expr) => {
                                Some(cx.map_ast_with_parent(AstNode::Expr(expr), node_id))
                            }
                        };
                        named_ports.push((port.span, name, value_id));
                    }
                    ast::PortConnData::Positional(ref expr) => {
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
                ast: inst,
                target: target_id,
                named_ports,
                pos_ports,
                has_wildcard_port,
            };
            Ok(HirNode::Inst(cx.arena().alloc_hir(hir)))
        }
        AstNode::TypeParam(param, decl) => {
            let hir = hir::TypeParam {
                id: node_id,
                name: decl.name,
                span: Span::union(param.span, decl.span),
                local: param.local,
                default: decl
                    .ty
                    .as_ref()
                    .map(|ty| cx.map_ast_with_parent(AstNode::Type(ty), node_id)),
            };
            Ok(HirNode::TypeParam(cx.arena().alloc_hir(hir)))
        }
        AstNode::ValueParam(param, decl) => {
            let hir = hir::ValueParam {
                id: node_id,
                name: decl.name,
                span: Span::union(param.span, decl.span),
                local: param.local,
                ty: cx.map_ast_with_parent(AstNode::Type(&decl.ty), node_id),
                default: decl
                    .expr
                    .as_ref()
                    .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), node_id)),
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
                    .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), node_id)),
                kind: hir::VarKind::Var,
            };
            Ok(HirNode::VarDecl(cx.arena().alloc_hir(hir)))
        }
        AstNode::NetDecl(name, decl, ty) => {
            // TODO(fschuiki): Map this to something different than a variable.
            let hir = hir::VarDecl {
                id: node_id,
                name: Spanned::new(name.name, name.name_span),
                span: Span::union(name.span, decl.span),
                ty: ty,
                init: name
                    .init
                    .as_ref()
                    .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), node_id)),
                kind: hir::VarKind::Net {
                    ty: decl.net_type,
                    kind: decl.kind,
                },
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
            let kind = match stmt.kind {
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
                            bug_span!(
                                stmt.span(),
                                cx,
                                "lowering of timing control {} to hir not implemented",
                                stmt
                            );
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
                    kind,
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
                        kind,
                    }
                }
                ast::AssertionStmt { .. } => {
                    cx.emit(
                        DiagBuilder2::warning("unsupported: immediate assertion; ignored")
                            .span(stmt.human_span()),
                    );
                    hir::StmtKind::Null
                }
                _ => {
                    error!("{:#?}", stmt);
                    bug_span!(
                        stmt.span(),
                        cx,
                        "lowering of {:?} to hir not implemented",
                        stmt
                    );
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
            let main_body = lower_module_block(cx, node_id, &gen.main_block.items, false, false)?;
            let else_body = match gen.else_block {
                Some(ref else_block) => Some(lower_module_block(
                    cx,
                    node_id,
                    &else_block.items,
                    false,
                    false,
                )?),
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
            let body = lower_module_block(cx, rib, &gen.block.items, false, false)?;
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
                span: decl.span,
                name: decl.name,
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
                span: def.span,
                name: def.name,
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
                kind: hir::VarKind::Var,
            };
            Ok(HirNode::VarDecl(cx.arena().alloc_hir(hir)))
        }
        AstNode::Package(p) => lower_package(cx, node_id, p),
        AstNode::EnumVariant(var, decl, index) => {
            let hir = hir::EnumVariant {
                id: node_id,
                name: var.name,
                span: var.span,
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
        AstNode::SubroutineDecl(decl) => {
            let hir = hir::Subroutine {
                id: node_id,
                name: decl.prototype.name,
                span: decl.span,
                kind: decl.prototype.kind,
                retty: decl
                    .prototype
                    .retty
                    .as_ref()
                    .map(|ty| cx.map_ast_with_parent(AstNode::Type(ty), node_id)),
            };
            Ok(HirNode::Subroutine(cx.arena().alloc_hir(hir)))
        }
        _ => {
            error!("{:#?}", ast);
            cx.unimp_msg("lowering of", &ast)
        }
    }
}

/// Lower a module to HIR.
#[moore_derive::query]
pub(crate) fn hir_of_module<'a>(
    cx: &impl Context<'a>,
    ast: &'a ast::Module<'a>,
) -> Result<&'a hir::Module<'a>> {
    let mut next_rib = ast.id();

    // Allocate the imports in the module header.
    for import in &ast.imports {
        for item in &import.items {
            next_rib = cx.map_ast_with_parent(AstNode::Import(item), next_rib);
        }
    }

    // Allocate parameters.
    let mut params = Vec::new();
    for param in &ast.params {
        next_rib = alloc_param_decl(cx, param, next_rib, &mut params);
    }

    // Lower the module's ports.
    let ports_new = cx.canonicalize_ports(ast);
    next_rib = ports_new.tail_rib;

    // Lower the module body.
    let block = lower_module_block(cx, next_rib, &ast.items, true, false)?;

    // Create the HIR module.
    let hir = hir::Module {
        ast,
        ports_new,
        params: cx.arena().alloc_ids(params),
        last_rib: block.last_rib,
        block,
    };
    let hir = cx.arena().alloc_hir(hir);

    // Internalize the ports.
    for port in &hir.ports_new.int {
        cx.intern_hir(port.id, HirNode::IntPort(port));
    }
    for port in &hir.ports_new.ext_pos {
        cx.intern_hir_with_parent(port.id, HirNode::ExtPort(port), ast.id());
    }

    Ok(hir)
}

/// Lower an interface to HIR.
#[moore_derive::query]
pub(crate) fn hir_of_interface<'a>(
    cx: &impl Context<'a>,
    ast: &'a ast::Interface<'a>,
) -> Result<&'a hir::Interface<'a>> {
    // Lower the interface's ports.
    let ports = cx.canonicalize_ports(ast);

    // Lower the interface body.
    let block = lower_module_block(cx, ast.id(), &ast.items, true, true)?;

    // Create the HIR node.
    let hir = hir::Interface { ast, ports, block };
    let hir = cx.arena().alloc_hir(hir);

    // Internalize the ports.
    for port in &hir.ports.int {
        cx.intern_hir(port.id, HirNode::IntPort(port));
    }
    for port in &hir.ports.ext_pos {
        cx.intern_hir_with_parent(port.id, HirNode::ExtPort(port), ast.id());
    }

    Ok(hir)
}

fn lower_module_block<'gcx>(
    cx: &impl Context<'gcx>,
    parent_rib: NodeId,
    items: impl IntoIterator<Item = &'gcx ast::Item<'gcx>>,
    allow_ports: bool,
    allow_modports: bool,
) -> Result<hir::ModuleBlock> {
    let mut next_rib = parent_rib;
    let mut insts = Vec::new();
    let mut decls = Vec::new();
    let mut procs = Vec::new();
    let mut gens = Vec::new();
    let mut params = Vec::new();
    let mut assigns = Vec::new();
    for item in items {
        match item.data {
            ast::ItemData::Dummy => (),
            ast::ItemData::ModuleDecl(ref decl) => {
                let id = cx.map_ast_with_parent(AstNode::Module(decl), next_rib);
                next_rib = id;
                procs.push(id);
            }
            ast::ItemData::PackageDecl(ref decl) => {
                let id = cx.map_ast_with_parent(AstNode::Package(decl), next_rib);
                next_rib = id;
                procs.push(id);
            }
            ast::ItemData::InterfaceDecl(ref decl) => {
                // let id = cx.map_ast_with_parent(AstNode::Interface(decl), next_rib);
                // next_rib = id;
                // procs.push(id);
                cx.emit(
                    DiagBuilder2::warning("unsupported: interface declaration; ignored")
                        .span(decl.span),
                );
            }
            ast::ItemData::ProgramDecl(ref _decl) => {
                // let id = cx.map_ast_with_parent(AstNode::Program(decl), next_rib);
                // next_rib = id;
                // procs.push(id);
                cx.emit(DiagBuilder2::warning(
                    "unsupported: program declaration; ignored",
                ));
            }
            ast::ItemData::Inst(ref inst) => {
                let target_id = cx.map_ast_with_parent(AstNode::InstTarget(inst), next_rib);
                next_rib = target_id;
                trace!("instantiation target `{}` => {:?}", inst.target, target_id);
                for inst in &inst.names {
                    let inst_id = cx.map_ast_with_parent(AstNode::Inst(inst, target_id), next_rib);
                    trace!("instantiation `{}` => {:?}", inst.name, inst_id);
                    next_rib = inst_id;
                    insts.push(inst_id);
                }
            }
            ast::ItemData::VarDecl(ref decl) => {
                next_rib = alloc_var_decl(cx, decl, next_rib, &mut decls);
            }
            ast::ItemData::NetDecl(ref decl) => {
                next_rib = alloc_net_decl(cx, decl, next_rib, &mut decls);
            }
            ast::ItemData::Procedure(ref prok) => {
                let id = cx.map_ast_with_parent(AstNode::Proc(prok), next_rib);
                next_rib = id;
                procs.push(id);
            }
            ast::ItemData::GenerateIf(ref gen) => {
                let id = cx.map_ast_with_parent(AstNode::GenIf(gen), next_rib);
                next_rib = id;
                gens.push(id);
            }
            ast::ItemData::GenerateFor(ref gen) => {
                let id = cx.map_ast_with_parent(AstNode::GenFor(gen), next_rib);
                next_rib = id;
                gens.push(id);
            }
            ast::ItemData::GenerateCase(ref gen) => {
                let id = cx.map_ast_with_parent(AstNode::GenCase(gen), next_rib);
                next_rib = id;
                gens.push(id);
            }
            ast::ItemData::ParamDecl(ref param) => {
                next_rib = alloc_param_decl(cx, param, next_rib, &mut params);
            }
            ast::ItemData::Typedef(ref def) => {
                let id = cx.map_ast_with_parent(AstNode::Typedef(def), next_rib);
                next_rib = id;
            }
            ast::ItemData::ContAssign(ref assign) => {
                for &(ref lhs, ref rhs) in &assign.assignments {
                    let id =
                        cx.map_ast_with_parent(AstNode::ContAssign(assign, lhs, rhs), next_rib);
                    next_rib = id;
                    assigns.push(id);
                }
            }
            ast::ItemData::ImportDecl(ref decl) => {
                for item in &decl.items {
                    let id = cx.map_ast_with_parent(AstNode::Import(item), next_rib);
                    next_rib = id;
                }
            }
            ast::ItemData::PortDecl(ref decl) => {
                if !allow_ports {
                    cx.emit(
                        DiagBuilder2::error("misplaced port declaration")
                            .span(decl.span)
                            .add_note(
                                "Port declarations can only appear directly in a module body",
                            ),
                    );
                }
            }
            ast::ItemData::ModportDecl(ref _decl) if allow_modports => (),
            ast::ItemData::ModportDecl(ref decl) => {
                cx.emit(
                    DiagBuilder2::error("modport declaration in module")
                        .span(decl.span)
                        .add_note("Modport declarations can only appear in an interface"),
                );
            }
            ast::ItemData::ClassDecl(ref decl) => {
                cx.emit(
                    DiagBuilder2::warning("unsupported: class declaration; ignored")
                        .span(decl.span),
                );
            }
            ast::ItemData::SubroutineDecl(ref decl) => {
                let id = cx.map_ast_with_parent(AstNode::SubroutineDecl(decl), next_rib);
                next_rib = id;
            }
            ast::ItemData::Assertion(ref assert) => {
                cx.emit(
                    DiagBuilder2::warning("unsupported: concurrent assertion; ignored")
                        .span(assert.span),
                );
            }

            // The remaining items don't need an HIR representation.
            ast::ItemData::DpiDecl(..)
            | ast::ItemData::GenvarDecl(..)
            | ast::ItemData::GenerateRegion(..) => (),
        }
    }
    Ok(hir::ModuleBlock {
        insts,
        decls,
        procs,
        gens,
        params,
        assigns,
        last_rib: next_rib,
    })
}

fn lower_type<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    ty: &'gcx ast::Type<'gcx>,
) -> Result<HirNode<'gcx>> {
    let mut kind = match ty.kind.data {
        ast::ImplicitType => hir::TypeKind::Implicit,
        ast::VoidType => hir::TypeKind::Builtin(hir::BuiltinType::Void),
        ast::BitType => hir::TypeKind::Builtin(hir::BuiltinType::Bit),
        ast::RegType => hir::TypeKind::Builtin(hir::BuiltinType::Logic),
        ast::LogicType => hir::TypeKind::Builtin(hir::BuiltinType::Logic),
        ast::ByteType => hir::TypeKind::Builtin(hir::BuiltinType::Byte),
        ast::ShortIntType => hir::TypeKind::Builtin(hir::BuiltinType::ShortInt),
        ast::IntType => hir::TypeKind::Builtin(hir::BuiltinType::Int),
        ast::IntegerType => hir::TypeKind::Builtin(hir::BuiltinType::Integer),
        ast::LongIntType => hir::TypeKind::Builtin(hir::BuiltinType::LongInt),
        ast::StringType => hir::TypeKind::Builtin(hir::BuiltinType::String),
        ast::TimeType => hir::TypeKind::Builtin(hir::BuiltinType::Time),
        ast::NamedType(name) => hir::TypeKind::Named(name),
        ast::StructType(ref def) => {
            let mut fields = vec![];
            let mut next_rib = node_id;
            for member in &def.members {
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
            name,
        ),
        ast::EnumType(ref enm) => {
            let repr_ty = &enm.base_type;
            let names = &enm.variants;
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
                variants.push((name.name, next_rib));
            }
            hir::TypeKind::Enum(variants, ty)
        }
        ast::TypeRef(ref arg) => {
            // Special care is needed here for types that were mistakenly parsed
            // as an expression.
            match *arg.as_ref() {
                ast::TypeOrExpr::Expr(expr) => match expr.data {
                    ast::IdentExpr(n) => {
                        let binding = cx.resolve_upwards_or_error(n, node_id)?;
                        match cx.hir_of(binding)? {
                            HirNode::TypeParam(..) | HirNode::Typedef(..) => {
                                let ty = cx.arena().alloc_ast_type(ast::Type::new(
                                    expr.span,
                                    ast::TypeData {
                                        kind: ast::TypeKind::new(expr.span, ast::NamedType(n)),
                                        sign: ast::TypeSign::None,
                                        dims: vec![],
                                    },
                                ));
                                ty.link_attach(expr, expr.order());
                                hir::TypeKind::RefType(
                                    cx.map_ast_with_parent(AstNode::Type(ty), node_id),
                                )
                            }
                            _ => hir::TypeKind::RefExpr(
                                cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
                            ),
                        }
                    }
                    _ => {
                        hir::TypeKind::RefExpr(cx.map_ast_with_parent(AstNode::Expr(expr), node_id))
                    }
                },
                ast::TypeOrExpr::Type(ty) => {
                    hir::TypeKind::RefType(cx.map_ast_with_parent(AstNode::Type(ty), node_id))
                }
            }
        }
        ast::ChandleType
        | ast::VirtIntfType(..)
        | ast::EventType
        | ast::MailboxType
        | ast::ImplicitSignedType
        | ast::ImplicitUnsignedType
        | ast::ShortRealType
        | ast::RealType
        | ast::RealtimeType
        | ast::SpecializedType(..)
        | ast::ScopedType { .. } => {
            error!("{:#?}", ty);
            bug_span!(
                ty.span(),
                cx,
                "lowering of {} to hir not implemented",
                ty.format_indefinite()
            );
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
    expr: &'gcx ast::Expr<'gcx>,
) -> Result<HirNode<'gcx>> {
    let kind = lower_expr_inner(cx, node_id, expr)?;
    let hir = hir::Expr {
        id: node_id,
        span: expr.span,
        kind: kind,
        dummy: Default::default(),
    };
    Ok(HirNode::Expr(cx.arena().alloc_hir(hir)))
}

fn lower_expr_inner<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    expr: &'gcx ast::Expr<'gcx>,
) -> Result<hir::ExprKind> {
    use crate::syntax::token::{Lit, Op};
    Ok(match expr.data {
        ast::LiteralExpr(Lit::Number(v, None)) => match v.as_str().parse() {
            Ok(v) => hir::ExprKind::IntConst {
                width: 32,
                value: v,
                signed: true,
                special_bits: BitVec::from_elem(32, false),
                x_bits: BitVec::from_elem(32, false),
            },
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

        ast::LiteralExpr(Lit::BasedInteger(maybe_size, signed, base, value)) => {
            let value_str = value.as_str();

            // Parse the number's value.
            let parsed = BigInt::parse_bytes(
                value_str
                    .chars()
                    .map(|c| match c {
                        'x' | 'X' | 'z' | 'Z' | '?' => '0',
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

            // Parse the size and verify the number fits.
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
                cx.emit(
                    DiagBuilder2::warning(format!("`{}` is too large", value,))
                        .span(expr.span)
                        .add_note(format!(
                            "constant is {} bits wide, but the value `{}{}` needs {} bits to not \
                             be truncated",
                            size, base, value, size_needed
                        )),
                );
            }

            // Identify the special bits (x and z) in the input.
            // TODO(fschuiki): Decimal literals are not handled properly.
            let bit_iter = value_str.chars().flat_map(|c| {
                std::iter::repeat(c).take(match base {
                    'h' => 4,
                    'o' => 3,
                    'b' => 1,
                    _ => 0,
                })
            });
            let special_bits: BitVec = bit_iter
                .clone()
                .map(|c| match c {
                    'x' | 'X' | 'z' | 'Z' | '?' => true,
                    _ => false,
                })
                .collect();
            let x_bits: BitVec = bit_iter
                .clone()
                .map(|c| match c {
                    'x' | 'X' => true,
                    _ => false,
                })
                .collect();

            // Assemble the HIR node.
            hir::ExprKind::IntConst {
                width: size,
                value: parsed,
                signed,
                special_bits,
                x_bits,
            }
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

        ast::LiteralExpr(Lit::Str(value)) => {
            hir::ExprKind::StringConst(Spanned::new(value, expr.span))
        }

        ast::IdentExpr(ident) => hir::ExprKind::Ident(ident),
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
            cx.map_ast_with_parent(AstNode::Expr(arg), node_id),
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
                // TODO: Make these separate operators.
                Op::CaseEq => hir::BinaryOp::Eq,
                Op::CaseNeq => hir::BinaryOp::Neq,
                // TODO: Make these separate operators.
                Op::WildcardEq => hir::BinaryOp::Eq,
                Op::WildcardNeq => hir::BinaryOp::Neq,
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
                    error!("Offending operator is {:?}", op);
                    return Err(());
                }
            },
            cx.map_ast_with_parent(AstNode::Expr(lhs), node_id),
            cx.map_ast_with_parent(AstNode::Expr(rhs), node_id),
        ),
        ast::MemberExpr { ref expr, name } => {
            hir::ExprKind::Field(cx.map_ast_with_parent(AstNode::Expr(expr), node_id), name)
        }
        ast::IndexExpr {
            ref indexee,
            ref index,
        } => {
            let indexee = cx.map_ast_with_parent(AstNode::Expr(indexee), node_id);
            let mode = lower_index_mode(cx, index, node_id);
            // let mode = match index.data {
            //     ast::RangeExpr {
            //         mode,
            //         ref lhs,
            //         ref rhs,
            //     } => hir::IndexMode::Many(
            //         mode,
            //         cx.map_ast_with_parent(AstNode::Expr(lhs), node_id),
            //         cx.map_ast_with_parent(AstNode::Expr(rhs), node_id),
            //     ),
            //     _ => hir::IndexMode::One(cx.map_ast_with_parent(AstNode::Expr(index), node_id)),
            // };
            hir::ExprKind::Index(indexee, mode)
        }
        ast::CallExpr(ref callee, ref args) => match callee.data {
            ast::SysIdentExpr(ident) => {
                let map_unary = || {
                    Ok(match args.as_slice() {
                        [ast::CallArg {
                            expr: Some(ref arg),
                            ..
                        }] => cx.map_ast_with_parent(AstNode::Expr(arg), node_id),
                        _ => {
                            cx.emit(
                                DiagBuilder2::error(format!("`{}` takes one argument", ident))
                                    .span(expr.human_span()),
                            );
                            return Err(());
                        }
                    })
                };
                hir::ExprKind::Builtin(match &*ident.value.as_str() {
                    "clog2" => hir::BuiltinCall::Clog2(map_unary()?),
                    "bits" => hir::BuiltinCall::Bits(map_unary()?),
                    "signed" => hir::BuiltinCall::Signed(map_unary()?),
                    "unsigned" => hir::BuiltinCall::Unsigned(map_unary()?),
                    _ => {
                        cx.emit(
                            DiagBuilder2::warning(format!("`${}` not supported; ignored", ident))
                                .span(expr.human_span()),
                        );
                        hir::BuiltinCall::Unsupported
                    }
                })
            }
            ast::IdentExpr(name) => {
                let target =
                    cx.resolve_upwards_or_error(name, cx.parent_node_id(node_id).unwrap())?;
                hir::ExprKind::FunctionCall(
                    target,
                    args.iter()
                        .map(|arg| lower_call_arg(cx, arg, node_id))
                        .collect(),
                )
            }
            _ => {
                error!("{:#?}", callee);
                cx.emit(
                    DiagBuilder2::warning(format!(
                        "`{}` is not something that can be called",
                        expr.span().extract()
                    ))
                    .span(expr.human_span()),
                );
                return Err(());
            }
        },
        ast::TernaryExpr {
            ref cond,
            ref true_expr,
            ref false_expr,
        } => hir::ExprKind::Ternary(
            cx.map_ast_with_parent(AstNode::Expr(cond), node_id),
            cx.map_ast_with_parent(AstNode::Expr(true_expr), node_id),
            cx.map_ast_with_parent(AstNode::Expr(false_expr), node_id),
        ),
        ast::ScopeExpr(ref expr, name) => hir::ExprKind::Scope(
            cx.map_ast_with_parent(AstNode::Expr(expr.as_ref()), node_id),
            name,
        ),
        ast::PatternExpr(ref fields) if fields.is_empty() => {
            cx.emit(DiagBuilder2::error("pattern must have at least one field").span(expr.span()));
            return Err(());
        }
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
                .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), node_id)),
            exprs
                .iter()
                .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), node_id))
                .collect(),
        ),
        ast::CastExpr(ref ty, ref expr) => {
            // Catch the corner case where a size cast looks like a type cast.
            if let ast::NamedType(n) = ty.kind.data {
                let binding =
                    cx.resolve_upwards_or_error(n, cx.parent_node_id(node_id).unwrap())?;
                match cx.hir_of(binding)? {
                    HirNode::TypeParam(..) | HirNode::Typedef(..) => hir::ExprKind::Cast(
                        cx.map_ast_with_parent(AstNode::Type(ty), node_id),
                        cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
                    ),
                    _ => {
                        let size_expr = cx
                            .arena()
                            .alloc_ast_expr(ast::Expr::new(ty.span, ast::IdentExpr(n)));
                        size_expr.link_attach(ty, ty.order());
                        hir::ExprKind::CastSize(
                            cx.map_ast_with_parent(AstNode::Expr(size_expr), node_id),
                            cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
                        )
                    }
                }
            } else {
                hir::ExprKind::Cast(
                    cx.map_ast_with_parent(AstNode::Type(ty), node_id),
                    cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
                )
            }
        }
        ast::CastSignExpr(sign, ref expr) => hir::ExprKind::CastSign(
            Spanned::new(
                match sign.value {
                    ast::TypeSign::Signed => ty::Sign::Signed,
                    ast::TypeSign::Unsigned => ty::Sign::Unsigned,
                    ast::TypeSign::None => unreachable!(),
                },
                sign.span,
            ),
            cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
        ),
        ast::CastSizeExpr(ref size_expr, ref expr) => hir::ExprKind::CastSize(
            cx.map_ast_with_parent(AstNode::Expr(size_expr), node_id),
            cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
        ),
        ast::InsideExpr(ref expr, ref ranges) => hir::ExprKind::Inside(
            cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
            ranges
                .iter()
                .map(|vr| match vr {
                    ast::ValueRange::Single(expr) => Spanned::new(
                        hir::InsideRange::Single(
                            cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
                        ),
                        expr.span,
                    ),
                    ast::ValueRange::Range { lo, hi, span } => Spanned::new(
                        hir::InsideRange::Range(
                            cx.map_ast_with_parent(AstNode::Expr(lo), node_id),
                            cx.map_ast_with_parent(AstNode::Expr(hi), node_id),
                        ),
                        *span,
                    ),
                })
                .collect(),
        ),
        _ => {
            error!("{:#1?}", expr);
            bug_span!(
                expr.span,
                cx,
                "lowering of {:?} to hir not implemented",
                expr
            );
        }
    })
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
    expr: &'gcx ast::EventExpr<'gcx>,
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
    stmt: &'gcx ast::Stmt<'gcx>,
    mut parent_id: NodeId,
) -> Result<Vec<NodeId>> {
    let mut ids = vec![];
    match stmt.kind {
        ast::GenvarDeclStmt(ref decls) => {
            for decl in decls {
                let id = cx.map_ast_with_parent(AstNode::GenvarDecl(decl), parent_id);
                ids.push(id);
                parent_id = id;
            }
        }
        _ => {
            cx.emit(
                DiagBuilder2::error(format!("{:#} is not a valid genvar initialization", stmt))
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
    param: &'gcx ast::ParamDecl<'gcx>,
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
    decl: &'gcx ast::VarDecl<'gcx>,
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

/// Allocate node IDs for a net declaration.
fn alloc_net_decl<'gcx>(
    cx: &impl Context<'gcx>,
    decl: &'gcx ast::NetDecl<'gcx>,
    mut next_rib: NodeId,
    into: &mut Vec<NodeId>,
) -> NodeId {
    let type_id = cx.map_ast_with_parent(AstNode::Type(&decl.ty), next_rib);
    next_rib = type_id;
    for name in &decl.names {
        let decl_id = cx.map_ast_with_parent(AstNode::NetDecl(name, decl, type_id), next_rib);
        next_rib = decl_id;
        into.push(decl_id);
    }
    next_rib
}

/// Allocate node IDs for a struct member.
fn alloc_struct_member<'gcx>(
    cx: &impl Context<'gcx>,
    member: &'gcx ast::StructMember<'gcx>,
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
    ast: &'gcx ast::Package<'gcx>,
) -> Result<HirNode<'gcx>> {
    let mut next_rib = node_id;
    let mut names = Vec::new();
    let mut decls = Vec::new();
    let mut params = Vec::new();
    for item in &ast.items {
        match item.data {
            ast::ItemData::VarDecl(ref decl) => {
                next_rib = alloc_var_decl(cx, decl, next_rib, &mut decls);
            }
            ast::ItemData::ParamDecl(ref param) => {
                next_rib = alloc_param_decl(cx, param, next_rib, &mut params);
            }
            ast::ItemData::Typedef(ref def) => {
                next_rib = cx.map_ast_with_parent(AstNode::Typedef(def), next_rib);
                names.push((def.name, next_rib));
            }
            ast::ItemData::SubroutineDecl(ref decl) => {
                warn!("ignoring unsupported subroutine `{}`", decl.prototype.name)
            }
            _ => {
                cx.emit(
                    DiagBuilder2::error(format!("{:#} cannot appear in a package", item))
                        .span(item.human_span()),
                );
                return Err(());
            }
        }
    }

    let hir = hir::Package {
        id: node_id,
        name: ast.name,
        span: ast.span,
        names,
        decls,
        params,
        last_rib: next_rib,
    };
    Ok(HirNode::Package(cx.arena().alloc_hir(hir)))
}

pub(crate) fn lower_index_mode<'gcx>(
    cx: &impl Context<'gcx>,
    index: &'gcx ast::Expr<'gcx>,
    parent: NodeId,
) -> hir::IndexMode {
    match index.data {
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
    }
}

/// Lower a function or method call argument to HIR.
fn lower_call_arg<'gcx>(
    cx: &impl Context<'gcx>,
    ast: &'gcx ast::CallArg<'gcx>,
    parent: NodeId,
) -> hir::CallArg {
    hir::CallArg {
        span: ast.span,
        name: ast.name.map(|n| Spanned::new(n, ast.name_span)),
        expr: ast
            .expr
            .as_ref()
            .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), parent)),
    }
}
