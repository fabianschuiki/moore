// Copyright (c) 2016-2020 Fabian Schuiki

//! An implementation of the visitor pattern for the HIR.
//!
//! This module defines the [`Visitor`] trait that allows the HIR tree graph to
//! be visited.

use super::{nodes::*, HirNode};
use crate::{
    common::{name::Name, source::Spanned, NodeId},
    Context,
};

/// A visitor of the HIR.
pub trait Visitor<'a>: Sized {
    /// The type of context that this visitor uses.
    type Context: Context<'a>;

    /// Get the context to be used to resolve queries.
    fn context(&self) -> &Self::Context;

    fn visit_node_with_id(&mut self, node_id: NodeId, lvalue: bool) {
        match self.context().hir_of(node_id) {
            Ok(x) => self.visit_node(x, lvalue),
            Err(()) => (),
        }
    }

    fn visit_node(&mut self, node: HirNode<'a>, lvalue: bool) {
        match node {
            HirNode::Module(x) => self.visit_module(x),
            HirNode::Proc(x) => self.visit_proc(x),
            HirNode::Stmt(x) => self.visit_stmt(x),
            HirNode::Expr(x) => self.visit_expr(x, lvalue),
            HirNode::EventExpr(x) => self.visit_event_expr(x),
            HirNode::Typedef(x) => self.visit_typedef(x),
            HirNode::VarDecl(x) => self.visit_var_decl(x),
            HirNode::Assign(x) => self.visit_assign(x),
            HirNode::IntPort(x) => self.visit_int_port(x),
            HirNode::ExtPort(x) => self.visit_ext_port(x),
            HirNode::Inst(x) => self.visit_inst(x),
            HirNode::InstTarget(x) => self.visit_inst_target(x),
            _ => (),
        }
    }

    fn visit_ident(&mut self, _ident: Spanned<Name>) {}
    fn visit_unary_op(&mut self, _op: UnaryOp) {}
    fn visit_binary_op(&mut self, _op: BinaryOp) {}

    fn visit_module(&mut self, module: &'a Module) {
        walk_module(self, module)
    }

    fn visit_proc(&mut self, prok: &'a Proc) {
        walk_proc(self, prok)
    }

    fn visit_stmt(&mut self, stmt: &'a Stmt) {
        walk_stmt(self, stmt)
    }

    fn visit_expr(&mut self, expr: &'a Expr, lvalue: bool) {
        walk_expr(self, expr, lvalue);
    }

    fn visit_timing_control(&mut self, ctrl: &'a TimingControl) {
        walk_timing_control(self, ctrl);
    }

    fn visit_event_expr(&mut self, expr: &'a EventExpr) {
        walk_event_expr(self, expr);
    }

    fn visit_event(&mut self, event: &'a Event) {
        walk_event(self, event);
    }

    fn visit_typedef(&mut self, typedef: &'a Typedef) {
        walk_typedef(self, typedef);
    }

    fn visit_var_decl(&mut self, decl: &'a VarDecl) {
        walk_var_decl(self, decl);
    }

    fn visit_assign(&mut self, assign: &'a Assign) {
        walk_assign(self, assign);
    }

    fn visit_int_port(&mut self, int_port: &'a IntPort) {
        walk_int_port(self, int_port);
    }

    fn visit_ext_port(&mut self, ext_port: &'a ExtPort) {
        walk_ext_port(self, ext_port);
    }

    fn visit_inst(&mut self, hir: &'a Inst) {
        walk_inst(self, hir);
    }

    fn visit_inst_target(&mut self, hir: &'a InstTarget) {
        walk_inst_target(self, hir);
    }
}

/// Walk the contents of a module.
pub fn walk_module<'a>(visitor: &mut impl Visitor<'a>, module: &'a Module) {
    for port in &module.ports_new.int {
        visitor.visit_node_with_id(port.id, false);
    }
    for port in &module.ports_new.ext_pos {
        visitor.visit_node_with_id(port.id, false);
    }
    for &id in module.params {
        visitor.visit_node_with_id(id, false);
    }
    walk_module_block(visitor, &module.block);
}

/// Walk the contents of a module block.
pub fn walk_module_block<'a>(visitor: &mut impl Visitor<'a>, blk: &'a ModuleBlock) {
    for &id in &blk.insts {
        visitor.visit_node_with_id(id, false);
    }
    for &id in &blk.decls {
        visitor.visit_node_with_id(id, false);
    }
    for &id in &blk.procs {
        visitor.visit_node_with_id(id, false);
    }
    for &id in &blk.gens {
        visitor.visit_node_with_id(id, false);
    }
    for &id in &blk.params {
        visitor.visit_node_with_id(id, false);
    }
    for &id in &blk.assigns {
        visitor.visit_node_with_id(id, false);
    }
}

/// Walk the contents of a procedure.
pub fn walk_proc<'a>(visitor: &mut impl Visitor<'a>, prok: &'a Proc) {
    visitor.visit_node_with_id(prok.stmt, false);
}

/// Walk the contents of a statement.
pub fn walk_stmt<'a>(visitor: &mut impl Visitor<'a>, stmt: &'a Stmt) {
    #[allow(unreachable_patterns)]
    match stmt.kind {
        StmtKind::Null => (),
        StmtKind::Block(ref stmts) => {
            for &id in stmts {
                visitor.visit_node_with_id(id, false);
            }
        }
        StmtKind::Assign { lhs, rhs, .. } => {
            visitor.visit_node_with_id(lhs, true);
            visitor.visit_node_with_id(rhs, false);
        }
        StmtKind::Timed { ref control, stmt } => {
            visitor.visit_timing_control(control);
            visitor.visit_node_with_id(stmt, false);
        }
        StmtKind::Expr(expr) => visitor.visit_node_with_id(expr, false),
        StmtKind::If {
            cond,
            main_stmt,
            else_stmt,
        } => {
            visitor.visit_node_with_id(cond, false);
            visitor.visit_node_with_id(main_stmt, false);
            if let Some(else_stmt) = else_stmt {
                visitor.visit_node_with_id(else_stmt, false);
            }
        }
        StmtKind::Loop { kind, body } => {
            match kind {
                LoopKind::Forever => (),
                LoopKind::Repeat(id) | LoopKind::While(id) | LoopKind::Do(id) => {
                    visitor.visit_node_with_id(id, false);
                }
                LoopKind::For(init, cond, step) => {
                    visitor.visit_node_with_id(init, false);
                    visitor.visit_node_with_id(cond, false);
                    visitor.visit_node_with_id(step, false);
                }
            }
            visitor.visit_node_with_id(body, false);
        }
        StmtKind::InlineGroup { ref stmts, .. } => {
            for &stmt in stmts {
                visitor.visit_node_with_id(stmt, false);
            }
        }
        StmtKind::Case {
            expr,
            ref ways,
            default,
            ..
        } => {
            visitor.visit_node_with_id(expr, false);
            for &(ref exprs, stmt) in ways {
                for &expr in exprs {
                    visitor.visit_node_with_id(expr, false);
                }
                visitor.visit_node_with_id(stmt, false);
            }
            if let Some(default) = default {
                visitor.visit_node_with_id(default, false);
            }
        }
    }
}

/// Walk the contents of an expression.
pub fn walk_expr<'a>(visitor: &mut impl Visitor<'a>, expr: &'a Expr, lvalue: bool) {
    match expr.kind {
        ExprKind::Builtin(BuiltinCall::Unsupported)
        | ExprKind::IntConst { .. }
        | ExprKind::UnsizedConst(_)
        | ExprKind::TimeConst(_)
        | ExprKind::StringConst(_) => (),
        ExprKind::Ident(x) => {
            visitor.visit_ident(x);
        }
        ExprKind::Unary(op, arg) => {
            visitor.visit_unary_op(op);
            visitor.visit_node_with_id(arg, lvalue);
        }
        ExprKind::Binary(op, lhs, rhs) => {
            visitor.visit_binary_op(op);
            visitor.visit_node_with_id(lhs, lvalue);
            visitor.visit_node_with_id(rhs, lvalue);
        }
        ExprKind::Field(expr, _) => {
            visitor.visit_node_with_id(expr, lvalue);
        }
        ExprKind::Index(expr, mode) => {
            visitor.visit_node_with_id(expr, lvalue);
            match mode {
                IndexMode::One(expr) => visitor.visit_node_with_id(expr, false),
                IndexMode::Many(_, lhs, rhs) => {
                    visitor.visit_node_with_id(lhs, false);
                    visitor.visit_node_with_id(rhs, false);
                }
            }
        }
        ExprKind::Builtin(BuiltinCall::Clog2(arg))
        | ExprKind::Builtin(BuiltinCall::Bits(arg))
        | ExprKind::Builtin(BuiltinCall::Signed(arg))
        | ExprKind::Builtin(BuiltinCall::Unsigned(arg)) => {
            visitor.visit_node_with_id(arg, false);
        }
        ExprKind::Ternary(cond, true_expr, false_expr) => {
            visitor.visit_node_with_id(cond, false);
            visitor.visit_node_with_id(true_expr, lvalue);
            visitor.visit_node_with_id(false_expr, lvalue);
        }
        ExprKind::Scope(expr, _) => {
            visitor.visit_node_with_id(expr, false);
        }
        ExprKind::PositionalPattern(ref exprs) => {
            for &expr in exprs {
                visitor.visit_node_with_id(expr, lvalue);
            }
        }
        ExprKind::NamedPattern(ref mappings) => {
            for &(key, value) in mappings {
                match key {
                    PatternMapping::Type(ty) => visitor.visit_node_with_id(ty, false),
                    PatternMapping::Member(expr) => visitor.visit_node_with_id(expr, false),
                    PatternMapping::Default => (),
                }
                visitor.visit_node_with_id(value, lvalue);
            }
        }
        ExprKind::RepeatPattern(count, ref exprs) => {
            visitor.visit_node_with_id(count, lvalue);
            for &expr in exprs {
                visitor.visit_node_with_id(expr, lvalue);
            }
        }
        ExprKind::Concat(repeat, ref exprs) => {
            if let Some(repeat) = repeat {
                visitor.visit_node_with_id(repeat, false);
            }
            for &expr in exprs {
                visitor.visit_node_with_id(expr, lvalue);
            }
        }
        ExprKind::Cast(ty, expr) => {
            visitor.visit_node_with_id(ty, false);
            visitor.visit_node_with_id(expr, false);
        }
        ExprKind::CastSign(_, expr) => {
            visitor.visit_node_with_id(expr, false);
        }
        ExprKind::CastSize(size_expr, expr) => {
            visitor.visit_node_with_id(size_expr, false);
            visitor.visit_node_with_id(expr, false);
        }
        ExprKind::Inside(expr, ref ranges) => {
            visitor.visit_node_with_id(expr, false);
            for r in ranges {
                match r.value {
                    InsideRange::Single(expr) => visitor.visit_node_with_id(expr, false),
                    InsideRange::Range(lo, hi) => {
                        visitor.visit_node_with_id(lo, false);
                        visitor.visit_node_with_id(hi, false);
                    }
                }
            }
        }
        ExprKind::FunctionCall(_, ref args) => {
            for &arg in args {
                if let Some(expr) = arg.expr {
                    visitor.visit_node_with_id(expr, false);
                }
            }
        }
    }
}

/// Walk the contents of a timing control block.
pub fn walk_timing_control<'a>(visitor: &mut impl Visitor<'a>, ctrl: &'a TimingControl) {
    match *ctrl {
        TimingControl::Delay(id) => visitor.visit_node_with_id(id, false),
        TimingControl::ImplicitEvent => (),
        TimingControl::ExplicitEvent(id) => visitor.visit_node_with_id(id, false),
    }
}

/// Walk the contents of an event expression.
pub fn walk_event_expr<'a>(visitor: &mut impl Visitor<'a>, expr: &'a EventExpr) {
    for event in &expr.events {
        visitor.visit_event(event);
    }
}

/// Walk the contents of an event.
pub fn walk_event<'a>(visitor: &mut impl Visitor<'a>, event: &'a Event) {
    visitor.visit_node_with_id(event.expr, false);
    for &iff in &event.iff {
        visitor.visit_node_with_id(iff, false);
    }
}

/// Walk the contents of a typedef.
pub fn walk_typedef<'a>(visitor: &mut impl Visitor<'a>, typedef: &'a Typedef) {
    visitor.visit_node_with_id(typedef.ty, false);
}

/// Walk the contents of a variable declaration.
pub fn walk_var_decl<'a>(visitor: &mut impl Visitor<'a>, decl: &'a VarDecl) {
    visitor.visit_node_with_id(decl.ty, false);
    if let Some(init) = decl.init {
        visitor.visit_node_with_id(init, false);
    }
}

/// Walk the contents of an assignment.
pub fn walk_assign<'a>(visitor: &mut impl Visitor<'a>, assign: &'a Assign) {
    visitor.visit_node_with_id(assign.lhs, true);
    visitor.visit_node_with_id(assign.rhs, false);
}

/// Walk the contents of an internal port.
pub fn walk_int_port<'a>(visitor: &mut impl Visitor<'a>, int_port: &'a IntPort) {
    if let Some(data) = &int_port.data {
        visitor.visit_node_with_id(data.ty, false);
        if let Some(default) = data.default {
            visitor.visit_node_with_id(default, false);
        }
    }
}

/// Walk the contents of an external port.
pub fn walk_ext_port<'a>(_visitor: &mut impl Visitor<'a>, _ext_port: &'a ExtPort) {}

/// Walk the contents of an instantiation.
pub fn walk_inst<'a>(visitor: &mut impl Visitor<'a>, hir: &'a Inst) {
    visitor.visit_node_with_id(hir.target, false);
    let pos_ports = hir.pos_ports.iter().flat_map(|&(_, p)| p);
    let named_ports = hir.named_ports.iter().flat_map(|&(_, _, p)| p);
    for p in pos_ports.chain(named_ports) {
        visitor.visit_node_with_id(p, false);
    }
}

/// Walk the contents of an instantiation target.
pub fn walk_inst_target<'a>(visitor: &mut impl Visitor<'a>, hir: &'a InstTarget) {
    let pos_params = hir.pos_params.iter().flat_map(|&(_, p)| p);
    let named_params = hir.named_params.iter().flat_map(|&(_, _, p)| p);
    for p in pos_params.chain(named_params) {
        visitor.visit_node_with_id(p, false);
    }
}
