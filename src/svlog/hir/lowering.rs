// Copyright (c) 2016-2020 Fabian Schuiki

//! Lowering of AST nodes to HIR nodes.

use crate::{
    ast_map::AstNode,
    crate_prelude::*,
    hir::{ExtPort, ExtPortExpr, ExtPortSelect, HirNode, IntPort, IntPortData, PortList},
};
use bit_vec::BitVec;
use num::BigInt;
use std::collections::HashMap;

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
        AstNode::Module(m) => lower_module(cx, node_id, m),
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
                name: Spanned::new(decl.name.name, decl.name.span),
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
            let main_body = lower_module_block(cx, node_id, &gen.main_block.items, false)?;
            let else_body = match gen.else_block {
                Some(ref else_block) => {
                    Some(lower_module_block(cx, node_id, &else_block.items, false)?)
                }
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
            let body = lower_module_block(cx, rib, &gen.block.items, false)?;
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
        AstNode::SubroutineDecl(decl) => {
            let hir = hir::Subroutine {
                id: node_id,
                name: Spanned::new(decl.prototype.name.name, decl.prototype.name.span),
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

    // Lower the module's ports.
    let ports_new = lower_module_ports(cx, &ast.ports, &ast.items, node_id, &mut next_rib);
    trace!("Lowered port list: {:#?}", ports_new);

    // Lower the module body.
    let block = lower_module_block(cx, next_rib, &ast.items, true)?;

    // Create the HIR module.
    let hir = hir::Module {
        id: node_id,
        name: Spanned::new(ast.name, ast.name_span),
        span: ast.span,
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
        cx.intern_hir_with_parent(port.id, HirNode::ExtPort(port), node_id);
    }

    Ok(HirNode::Module(hir))
}

/// Lower the ports of a module to HIR.
///
/// This is a fairly complex process due to the many degrees of freedom in SV.
/// Mainly we identify if the module uses an ANSI or non-ANSI style and then go
/// ahead and create the external and internal views of the ports.
fn lower_module_ports<'gcx>(
    cx: &impl Context<'gcx>,
    ast_ports: &'gcx [ast::Port],
    ast_items: &'gcx [ast::HierarchyItem],
    module: NodeId,
    next_rib: &mut NodeId,
) -> PortList {
    // First determined if the module uses ANSI or non-ANSI style. We do this by
    // Determining whether the first port has type, sign, and direction omitted.
    // If it has, the ports are declared in non-ANSI style.
    let (nonansi, first_span) = {
        let first = match ast_ports.first() {
            Some(p) => p,
            None => return PortList::default(),
        };
        let nonansi = match *first {
            ast::Port::Explicit { ref dir, .. } if dir.is_none() => true,
            ast::Port::Named {
                ref dir,
                ref kind,
                ref ty,
                ref expr,
                ..
            } if dir.is_none()
                && kind.is_none()
                && expr.is_none()
                && ty.data == ast::ImplicitType
                && ty.sign == ast::TypeSign::None
                && ty.dims.is_empty() =>
            {
                true
            }
            ast::Port::Implicit(_) => true,
            _ => false,
        };
        (nonansi, first.span())
    };
    debug!(
        "Module uses {} style",
        if nonansi { "non-ANSI" } else { "ANSI" }
    );

    // Create the external and internal port views.
    let partial_ports = match nonansi {
        true => lower_module_ports_nonansi(cx, ast_ports, ast_items, first_span, module),
        false => lower_module_ports_ansi(cx, ast_ports, ast_items, first_span, module),
    };
    trace!("Lowered ports: {:#?}", partial_ports);

    // Extend the internal port with default sign, port kind, and data type
    // where necessary in order to arrive at a final internal port list.
    let mut ports = vec![];
    let default_net_type = ast::NetType::Wire; // TODO: Make changeable by directive

    for port in partial_ports.int {
        let port_id = cx.alloc_id(port.span);

        // Determine the port kind.
        let kind = port.kind.unwrap_or_else(|| match port.dir {
            ast::PortDir::Input | ast::PortDir::Inout => ast::PortKind::Net(default_net_type),
            ast::PortDir::Output => {
                if port.ty == &ast::ImplicitType {
                    ast::PortKind::Net(default_net_type)
                } else {
                    ast::PortKind::Var
                }
            }
            ast::PortDir::Ref => ast::PortKind::Var,
        });

        // Verify that `inout` ports are of net kind, and `ref` ports are of var
        // kind.
        match (port.dir, kind) {
            (ast::PortDir::Inout, ast::PortKind::Var) => cx.emit(
                DiagBuilder2::error(format!(
                    "inout port `{}` must be a net; but is declared as variable",
                    port.name
                ))
                .span(port.name.span),
            ),
            (ast::PortDir::Ref, ast::PortKind::Net(_)) => cx.emit(
                DiagBuilder2::error(format!(
                    "ref port `{}` must be a variable; but is declared as net",
                    port.name
                ))
                .span(port.name.span),
            ),
            _ => (),
        }

        // Hook things up in the hierarchy.
        cx.set_ast(port_id, AstNode::Port(port.span));
        cx.set_parent(port_id, *next_rib);

        // Condense the details of this port, unless it is an inferred port
        // generated by an explicitly-named ANSI prot.
        let data = if port.inferred {
            None
        } else {
            // Determine the data type.
            let ty = if port.ty == &ast::ImplicitType {
                &ast::LogicType
            } else {
                port.ty
            };
            let ty_ast = cx.arena().alloc_ast_type(ast::Type {
                span: port.span,
                data: ty.clone(),
                sign: port.sign,
                dims: port.packed_dims.to_vec(),
            });
            let ty = cx.map_ast_with_parent(AstNode::Type(ty_ast), *next_rib);
            let _ = lower_type(cx, ty, ty_ast);

            // Allocate the default expression.
            let default = port
                .default
                .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), port_id));

            // Everything following the port can see the port.
            *next_rib = port_id;

            Some(IntPortData {
                ty,
                unpacked_dims: (),
                matching: None,
                default,
            })
        };

        // Package everything up in an internal port.
        ports.push(IntPort {
            id: port_id,
            module,
            span: port.span,
            name: port.name,
            dir: port.dir,
            kind,
            data,
        });
    }

    // Package the port list up.
    PortList {
        int: ports,
        ext_pos: partial_ports.ext_pos,
        ext_named: partial_ports.ext_named,
    }
}

/// Lower the ANSI ports of a module.
fn lower_module_ports_ansi<'gcx>(
    cx: &impl Context<'gcx>,
    ast_ports: &'gcx [ast::Port],
    ast_items: &'gcx [ast::HierarchyItem],
    first_span: Span,
    module: NodeId,
) -> PartialPortList<'gcx> {
    // Emit errors for any port declarations inside the module.
    for item in ast_items {
        let ast = match item {
            ast::HierarchyItem::PortDecl(pd) => pd,
            _ => continue,
        };
        cx.emit(
            DiagBuilder2::error("port declaration in body of ANSI-style module")
                .span(ast.span)
                .add_note("Modules with an ANSI-style port list cannot have port declarations in the body.")
                .add_note("Consider using non-ANSI style.")
                .add_note("First port uses ANSI style:")
                .span(first_span),
        );
    }

    // Ports have a rather sticky way of tracking types, signs, dimensions, etc.
    // Keep a list of "carry" variables that carry over the previous port's
    // details over to the next port. Initialize with the default mandated by
    // the standard.
    let mut carry_dir = ast::PortDir::Inout;
    let mut carry_kind: Option<ast::PortKind> = None;
    let mut carry_ty = &ast::LogicType;
    let mut carry_sign = ast::TypeSign::None;
    let mut carry_packed_dims: &[ast::TypeDim] = &[];

    // Map each of the ports in the list.
    let mut int_ports: Vec<PartialPort> = vec![];
    let mut ext_pos: Vec<ExtPort> = vec![];
    let mut ext_named: HashMap<Name, usize> = HashMap::new();
    let mut explicit_named: HashMap<(ast::PortDir, Name), usize> = HashMap::new();

    for port in ast_ports {
        let port = match port {
            // [direction] [net_type|"var"] type_or_implicit ident {dimension} ["=" expr]
            ast::Port::Named {
                span,
                dir,
                kind,
                ty,
                name,
                dims: unpacked_dims,
                expr,
            } => {
                // If no direction has been provided, use the one carried over
                // from the previous port.
                let dir = dir.unwrap_or(carry_dir);

                // If no port kind has been provided, use the one carried over
                // from the previous port.
                let kind = kind.or(carry_kind);

                // If no port type has been provided, use the one carried over
                //  from the previous port.
                let (ty, sign, packed_dims) = if ty.data == ast::ImplicitType
                    && ty.sign == ast::TypeSign::None
                    && ty.dims.is_empty()
                {
                    (carry_ty, carry_sign, carry_packed_dims)
                } else {
                    (&ty.data, ty.sign, ty.dims.as_slice())
                };

                // Keep the direction, kind, and type around for the next port
                // in the list, which might want to inherit them.
                carry_dir = dir;
                carry_kind = kind;
                carry_ty = ty;
                carry_sign = sign;
                carry_packed_dims = packed_dims;

                let data = PartialPort {
                    name: Spanned::new(name.name, name.span),
                    span: *span,
                    kind,
                    dir,
                    sign,
                    ty,
                    packed_dims,
                    unpacked_dims,
                    default: expr.as_ref(),
                    inferred: false,
                    var_decl: None,
                    net_decl: None,
                    match_ty: None,
                };
                let ext_port = ExtPort {
                    id: cx.alloc_id(*span),
                    module,
                    span: *span,
                    name: Some(data.name),
                    exprs: vec![ExtPortExpr {
                        port: int_ports.len(),
                        selects: vec![],
                    }],
                };
                int_ports.push(data);
                ext_port
            }

            // [direction] "." ident "(" [expr] ")"
            ast::Port::Explicit {
                span,
                dir,
                name,
                expr,
            } => {
                // If no direction has been provided, use the one carried
                // over from the previous port.
                let dir = dir.unwrap_or(carry_dir);

                // Clear the carry to some sane default. Not sure if this is the
                // expected behaviour, but there are no further details in the
                // standard. What a joke.
                carry_dir = dir;
                carry_kind = None;
                carry_ty = &ast::LogicType;
                carry_sign = ast::TypeSign::None;
                carry_packed_dims = &[];

                // Map the expression to a port expression.
                let pe = match expr {
                    Some(expr) => lower_port_expr(cx, expr, module),
                    None => vec![],
                };

                // Introduce inferred ports for each port reference in the port
                // expression.
                let pe = pe
                    .into_iter()
                    .map(|pr| {
                        let index =
                            *explicit_named
                                .entry((dir, pr.name.value))
                                .or_insert_with(|| {
                                    let index = int_ports.len();
                                    trace!("Adding inferred port {}", pr.name);
                                    int_ports.push(PartialPort {
                                        name: pr.name,
                                        span: *span,
                                        kind: None,
                                        dir,
                                        sign: ast::TypeSign::None,
                                        ty: &ast::ImplicitType, // inferred from expression
                                        packed_dims: &[],       // inferred from expression
                                        unpacked_dims: &[],
                                        default: None,
                                        inferred: true,
                                        var_decl: None,
                                        net_decl: None,
                                        match_ty: None,
                                    });
                                    index
                                });
                        ExtPortExpr {
                            port: index,
                            selects: pr.selects,
                        }
                    })
                    .collect();

                ExtPort {
                    id: cx.alloc_id(*span),
                    module,
                    span: *span,
                    name: Some(Spanned::new(name.name, name.span)),
                    exprs: pe,
                }
            }

            _ => {
                cx.emit(
                    DiagBuilder2::error("non-ANSI port in ANSI port list")
                        .span(port.span())
                        .add_note("First port uses ANSI style:")
                        .span(first_span),
                );
                error!("Invalid port: {:?}", port);
                continue;
            }
        };

        // Build a map of ordered and named port associations.
        if let Some(prev) = ext_named.insert(port.name.unwrap().value, ext_pos.len()) {
            cx.emit(
                DiagBuilder2::error(format!(
                    "port `{}` declared multiple times",
                    port.name.unwrap().value
                ))
                .span(port.name.unwrap().span)
                .add_note("Previous declaration was here:")
                .span(ext_pos[prev].name.unwrap().span),
            );
        }

        // Add the port to the internal and external port list.
        ext_pos.push(port);
    }

    PartialPortList {
        int: int_ports,
        ext_pos,
        ext_named: Some(ext_named),
    }
}

/// Lower the non-ANSI ports of a module.
fn lower_module_ports_nonansi<'gcx>(
    cx: &impl Context<'gcx>,
    ast_ports: &'gcx [ast::Port],
    ast_items: &'gcx [ast::HierarchyItem],
    first_span: Span,
    module: NodeId,
) -> PartialPortList<'gcx> {
    // As a first step, collect the ports declared inside the module body. These
    // will form the internal view of the ports.
    let mut decl_order: Vec<PartialPort> = vec![];
    let mut decl_names = HashMap::new();
    for item in ast_items {
        let ast = match item {
            ast::HierarchyItem::PortDecl(pd) => pd,
            _ => continue,
        };
        // trace!("Found {:#?}", ast);
        for name in &ast.names {
            let data = PartialPort {
                span: ast.span,
                name: Spanned::new(name.name, name.name_span),
                kind: ast.kind,
                dir: ast.dir,
                sign: ast.ty.sign,
                ty: &ast.ty.data,
                packed_dims: &ast.ty.dims,
                unpacked_dims: &name.dims,
                default: name.init.as_ref(),
                inferred: false,
                match_ty: None,
                var_decl: None,
                net_decl: None,
            };
            // trace!("Producing {:#?}", data);
            let index = decl_order.len();
            if let Some(prev) = decl_names.insert(data.name.value, index) {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "port `{}` declared multiple times",
                        data.name.value
                    ))
                    .span(data.name.span)
                    .add_note("Previous declaration was here:")
                    .span(decl_order[prev].name.span),
                );
            }
            decl_order.push(data);
        }
    }

    // As a second step, collect the variable and net declarations inside the
    // module body which further specify a port.
    for item in ast_items {
        match item {
            ast::HierarchyItem::VarDecl(vd) => {
                for name in &vd.names {
                    let index = match decl_names.get(&name.name) {
                        Some(&e) => e,
                        None => continue,
                    };
                    let entry = &mut decl_order[index];
                    if let Some(prev) = std::mem::replace(&mut entry.var_decl, Some((vd, name))) {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "port variable `{}` declared multiple times",
                                name.name
                            ))
                            .span(name.name_span)
                            .add_note("previous declaration was here:")
                            .span(prev.1.name_span),
                        );
                    }
                }
            }
            ast::HierarchyItem::NetDecl(nd) => {
                for name in &nd.names {
                    let index = match decl_names.get(&name.name) {
                        Some(&e) => e,
                        None => continue,
                    };
                    let entry = &mut decl_order[index];
                    if let Some(prev) = std::mem::replace(&mut entry.net_decl, Some((nd, name))) {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "port net `{}` declared multiple times",
                                name.name
                            ))
                            .span(name.name_span)
                            .add_note("previous declaration was here:")
                            .span(prev.1.name_span),
                        );
                    }
                }
            }
            _ => continue,
        }
    }

    // As a third step, merge the port declarations with the optional variable
    // and net declarations.
    for port in &mut decl_order {
        // Check if the port is already complete, that is, already has a net or
        // variable type. In that case it's an error to provide an additional
        // variable or net declaration that goes with it.
        if port.kind.is_some() || *port.ty != ast::ImplicitType {
            for span in port
                .var_decl
                .iter()
                .map(|x| x.1.span)
                .chain(port.net_decl.iter().map(|x| x.1.span))
            {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "port `{}` is complete; additional declaration forbidden",
                        port.name
                    ))
                    .span(span)
                    .add_note(
                        "Port already has a net/variable type. \
                        Cannot declare an additional net/variable with the same \
                        name.",
                    )
                    .add_note("Port declaration was here:")
                    .span(port.span),
                );
            }
            port.var_decl = None;
            port.net_decl = None;
        }

        // Extract additional details of the port from optional variable and net
        // declarations.
        let (add_span, add_ty, add_sign, add_packed, add_unpacked) =
            match (port.var_decl, port.net_decl) {
                // Inherit details from a variable declaration.
                (Some(vd), None) => {
                    // TODO: Pretty sure that this can never happen, since a port
                    // which already provides this information is considered
                    // complete.
                    if port.kind.is_some() && port.kind != Some(ast::PortKind::Var) {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "net port `{}` redeclared as variable",
                                port.name
                            ))
                            .span(vd.1.span)
                            .add_note("Port declaration was here:")
                            .span(port.span),
                        );
                    }
                    port.kind = Some(ast::PortKind::Var);
                    (
                        vd.1.name_span,
                        &vd.0.ty.data,
                        vd.0.ty.sign,
                        &vd.0.ty.dims,
                        &vd.1.dims,
                    )
                }
                // Inherit details from a net declaration.
                (None, Some(nd)) => {
                    // TODO: Pretty sure that this can never happen, since a port
                    // which already provides this information is considered
                    // complete.
                    if port.kind.is_some() && port.kind == Some(ast::PortKind::Var) {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "variable port `{}` redeclared as net",
                                port.name
                            ))
                            .span(nd.1.span)
                            .add_note("Port declaration was here:")
                            .span(port.span),
                        );
                    }
                    port.kind = Some(ast::PortKind::Net(nd.0.net_type));
                    (
                        nd.1.name_span,
                        &nd.0.ty.data,
                        nd.0.ty.sign,
                        &nd.0.ty.dims,
                        &nd.1.dims,
                    )
                }
                // Handle the case where both are present.
                (Some(vd), Some(nd)) => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "port `{}` doubly declared as variable and net",
                            port.name
                        ))
                        .span(vd.1.span)
                        .span(nd.1.span)
                        .add_note("Port declaration was here:")
                        .span(port.span),
                    );
                    continue;
                }
                // Otherwise we keep things as they are.
                (None, None) => continue,
            };

        // Merge the sign.
        match (port.sign, add_sign) {
            (a, b) if a == b => port.sign = a,
            (a, ast::TypeSign::None) => port.sign = a,
            (ast::TypeSign::None, b) => port.sign = b,
            (_, _) => {
                cx.emit(
                    DiagBuilder2::error(format!("port `{}` has contradicting signs", port.name))
                        .span(port.span)
                        .span(add_span),
                );
            }
        }

        // Merge the type.
        port.match_ty = Some((
            match (port.ty, add_ty) {
                (a, ast::ImplicitType) => {
                    port.ty = a;
                    None
                }
                (ast::ImplicitType, b) => {
                    port.ty = b;
                    None
                }
                (a, b) => {
                    port.ty = a;
                    Some(b)
                }
            },
            add_packed,
            add_unpacked,
        ));
    }

    // As a fourth step, go through the ports themselves and pair them up with
    // declarations inside the module body. This forms the external view of the
    // ports.
    let mut ext_pos: Vec<ExtPort> = vec![];
    let mut ext_named: HashMap<Name, usize> = HashMap::new();
    let mut any_unnamed = false;
    for port in ast_ports {
        let (span, name, exprs) = match port {
            // [direction] "." ident "(" [expr] ")"
            ast::Port::Explicit {
                span,
                dir: None,
                name,
                expr,
            } => {
                let name = Spanned::new(name.name, name.span);
                if let Some(expr) = expr {
                    let pe = lower_port_expr(cx, expr, module);
                    (*span, Some(name), pe)
                } else {
                    (*span, Some(name), vec![])
                }
            }

            // [direction] [net_type|"var"] type_or_implicit ident {dimension} ["=" expr]
            ast::Port::Named {
                span,
                dir: None,
                kind: None,
                ty:
                    ast::Type {
                        data: ast::ImplicitType,
                        sign: ast::TypeSign::None,
                        dims: packed_dims,
                        ..
                    },
                name,
                dims,
                expr: None,
            } if packed_dims.is_empty() => {
                let name = Spanned::new(name.name, name.span);
                // Now we have to deal with the problem that a port like
                // `foo[7:0]` is interpreted as a named type by the parser, but
                // is actually an implicit port. This is indicated by the dims
                // of the port being non-empty. In this case we recast the dims
                // as selects in a port expression.
                let selects = dims
                    .iter()
                    .map(|dim| match dim {
                        ast::TypeDim::Expr(index) => ExtPortSelect::Index(hir::IndexMode::One(
                            cx.map_ast_with_parent(AstNode::Expr(index), module),
                        )),
                        ast::TypeDim::Range(lhs, rhs) => {
                            ExtPortSelect::Index(hir::IndexMode::Many(
                                ast::RangeMode::Absolute,
                                cx.map_ast_with_parent(AstNode::Expr(lhs), module),
                                cx.map_ast_with_parent(AstNode::Expr(rhs), module),
                            ))
                        }
                        _ => {
                            cx.emit(
                                DiagBuilder2::error(format!(
                                    "invalid port range {}; on port `{}`",
                                    dim.desc_full(),
                                    name
                                ))
                                .span(*span),
                            );
                            ExtPortSelect::Error
                        }
                    })
                    .collect();
                let pe = vec![PartialPortExpr { name, selects }];

                // If dims are empty, then this is a named port. Otherwise it's
                // actually an implicit port with no name.
                if dims.is_empty() {
                    (*span, Some(name), pe)
                } else {
                    (*span, None, pe)
                }
            }

            // expr
            ast::Port::Implicit(expr) => {
                let pe = lower_port_expr(cx, expr, module);
                (expr.span, None, pe)
            }

            // Everything else is just an error.
            _ => {
                cx.emit(
                    DiagBuilder2::error("ANSI port in non-ANSI port list")
                        .span(port.span())
                        .add_note("First port uses non-ANSI style:")
                        .span(first_span),
                );
                error!("Invalid port: {:?}", port);
                continue;
            }
        };
        // trace!("Port {:?}: {:?}", name, exprs);

        // Resolve the port expressions to actual ports in the list.
        let exprs = exprs
            .into_iter()
            .flat_map(|expr| match decl_names.get(&expr.name.value) {
                Some(&index) => Some(ExtPortExpr {
                    port: index,
                    selects: expr.selects,
                }),
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "port `{}` not declared in module body",
                            expr.name
                        ))
                        .span(expr.name.span)
                        .add_note("Declare the port inside the module, e.g.:")
                        .add_note(format!("input {};", expr.name)),
                    );
                    None
                }
            })
            .collect();

        // Wrap things up in an external port.
        let port = ExtPort {
            id: cx.alloc_id(span),
            module,
            span,
            name,
            exprs,
        };

        // Build a map of ordered and named port associations.
        if let Some(name) = port.name {
            if ext_named.insert(name.value, ext_pos.len()).is_some() {
                // If the other port maps to the exact same thing, this is
                // admissible, but we lose the ability to perform named
                // connections.
                any_unnamed = true;
            }
        } else {
            any_unnamed = true;
        }
        ext_pos.push(port);
    }

    PartialPortList {
        int: decl_order,
        ext_pos,
        ext_named: if any_unnamed { None } else { Some(ext_named) },
    }
}

/// Lower an AST expression as a port expression.
///
/// ```plain
/// port_expression ::= port_reference | "{" port_reference {"," port_reference} "}"
/// ```
fn lower_port_expr<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &'gcx ast::Expr,
    parent: NodeId,
) -> Vec<PartialPortExpr> {
    match &expr.data {
        ast::ConcatExpr {
            repeat: None,
            exprs,
        } => exprs
            .iter()
            .flat_map(|expr| lower_port_ref(cx, expr, parent))
            .collect(),
        _ => lower_port_ref(cx, expr, parent).into_iter().collect(),
    }
}

/// Lower an AST expression as a port reference.
///
/// ```plain
/// port_reference ::= port_identifier constant_select
/// ```
fn lower_port_ref<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &'gcx ast::Expr,
    parent: NodeId,
) -> Option<PartialPortExpr> {
    match &expr.data {
        ast::IdentExpr(ident) => Some(PartialPortExpr {
            name: Spanned::new(ident.name, ident.span),
            selects: vec![],
        }),
        ast::IndexExpr { indexee, index } => {
            let mut pe = lower_port_ref(cx, indexee, parent)?;
            let mode = lower_index_mode(cx, index, parent);
            pe.selects.push(ExtPortSelect::Index(mode));
            Some(pe)
        }
        _ => {
            cx.emit(
                DiagBuilder2::error(format!(
                    "invalid port expression: `{}`",
                    expr.span.extract()
                ))
                .span(expr.span),
            );
            error!("{:?}", expr);
            None
        }
    }
}

#[derive(Debug)]
struct PartialPort<'a> {
    span: Span,
    name: Spanned<Name>,
    dir: ast::PortDir,
    kind: Option<ast::PortKind>,
    sign: ast::TypeSign,
    ty: &'a ast::TypeData,
    packed_dims: &'a [ast::TypeDim],
    unpacked_dims: &'a [ast::TypeDim],
    /// The default value assigned to this port if left unconnected.
    default: Option<&'a ast::Expr>,
    /// Whether the port characteristics are inferred from a declaration in the
    /// module. This is used for explicitly-named ANSI ports.
    inferred: bool,
    /// The variable declaration associated with a non-ANSI port.
    var_decl: Option<(&'a ast::VarDecl, &'a ast::VarDeclName)>,
    /// The net declaration associated with a non-ANSI port.
    net_decl: Option<(&'a ast::NetDecl, &'a ast::VarDeclName)>,
    /// Redundant type information which must be checked against the non-ANSI
    /// port later.
    match_ty: Option<(
        Option<&'a ast::TypeData>,
        &'a [ast::TypeDim],
        &'a [ast::TypeDim],
    )>,
}

#[derive(Debug)]
struct PartialPortExpr {
    name: Spanned<Name>,
    selects: Vec<ExtPortSelect>,
}

#[derive(Debug)]
struct PartialPortList<'a> {
    /// The internal ports.
    int: Vec<PartialPort<'a>>,
    /// The external ports, in order for positional connections. Port indices
    /// are indices into `int`.
    ext_pos: Vec<ExtPort>,
    /// The external ports, for named connections. Values are indices into
    /// `ext_pos`.
    ext_named: Option<HashMap<Name, usize>>,
}

fn lower_module_block<'gcx>(
    cx: &impl Context<'gcx>,
    parent_rib: NodeId,
    items: impl IntoIterator<Item = &'gcx ast::HierarchyItem>,
    allow_ports: bool,
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
            ast::HierarchyItem::Dummy => (),
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
            ast::HierarchyItem::NetDecl(ref decl) => {
                next_rib = alloc_net_decl(cx, decl, next_rib, &mut decls);
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
            ast::HierarchyItem::GenerateCase(ref gen) => {
                let id = cx.map_ast_with_parent(AstNode::GenCase(gen), next_rib);
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
            ast::HierarchyItem::PortDecl(ref decl) => {
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
            ast::HierarchyItem::ModportDecl(ref decl) => {
                cx.emit(
                    DiagBuilder2::error("modport declaration in module")
                        .span(decl.span)
                        .add_note("Modport declarations can only appear in an interface"),
                );
            }
            ast::HierarchyItem::ClassDecl(ref decl) => {
                cx.emit(
                    DiagBuilder2::warning("unsupported: class declaration; ignored")
                        .span(decl.span),
                );
            }
            ast::HierarchyItem::SubroutineDecl(ref decl) => {
                let id = cx.map_ast_with_parent(AstNode::SubroutineDecl(decl), next_rib);
                next_rib = id;
            }
            ast::HierarchyItem::Assertion(ref assert) => {
                cx.emit(
                    DiagBuilder2::warning("unsupported: concurrent assertion; ignored")
                        .span(assert.span),
                );
            }
            ast::HierarchyItem::GenvarDecl(..) | ast::HierarchyItem::GenerateRegion(..) => (),
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
    ty: &'gcx ast::Type,
) -> Result<HirNode<'gcx>> {
    let mut kind = match ty.data {
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
    let kind = match expr.data {
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
                cx.emit(DiagBuilder2::warning(format!(
                    "`{}` is too large",
                    value,
                )).span(expr.span).add_note(format!("constant is {} bits wide, but the value `{}{}` needs {} bits to not be truncated", size, base, value, size_needed)));
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
            cx.map_ast_with_parent(AstNode::Expr(lhs), node_id),
            cx.map_ast_with_parent(AstNode::Expr(rhs), node_id),
        ),
        ast::MemberExpr { ref expr, name } => hir::ExprKind::Field(
            cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
            Spanned::new(name.name, name.span),
        ),
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
                            DiagBuilder2::warning(format!(
                                "`${}` not supported; ignored",
                                ident.name
                            ))
                            .span(expr.human_span()),
                        );
                        hir::BuiltinCall::Unsupported
                    }
                })
            }
            ast::IdentExpr(name) => {
                let target = cx.resolve_upwards_or_error(
                    Spanned::new(name.name, name.span),
                    cx.parent_node_id(node_id).unwrap(),
                )?;
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
                .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), node_id)),
            exprs
                .iter()
                .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), node_id))
                .collect(),
        ),
        ast::CastExpr(ref ty, ref expr) => {
            // Catch the corner case where a size cast looks like a type cast.
            if let ast::NamedType(n) = ty.data {
                let binding = cx.resolve_upwards_or_error(
                    Spanned::new(n.name, n.span),
                    cx.parent_node_id(node_id).unwrap(),
                )?;
                match cx.hir_of(binding)? {
                    HirNode::TypeParam(..) | HirNode::Typedef(..) => hir::ExprKind::Cast(
                        cx.map_ast_with_parent(AstNode::Type(ty), node_id),
                        cx.map_ast_with_parent(AstNode::Expr(expr), node_id),
                    ),
                    _ => {
                        let size_expr = cx.arena().alloc_ast_expr(ast::Expr {
                            span: ty.span,
                            data: ast::IdentExpr(n),
                        });
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

/// Allocate node IDs for a net declaration.
fn alloc_net_decl<'gcx>(
    cx: &impl Context<'gcx>,
    decl: &'gcx ast::NetDecl,
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

fn lower_index_mode<'gcx>(
    cx: &impl Context<'gcx>,
    index: &'gcx ast::Expr,
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
    ast: &'gcx ast::CallArg,
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
