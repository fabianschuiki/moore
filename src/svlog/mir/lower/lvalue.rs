// Copyright (c) 2016-2019 Fabian Schuiki

//! Expression lvalue lowering to MIR.

use crate::{
    crate_prelude::*,
    hir::HirNode,
    mir::{lower::rvalue::compute_indexing, lvalue::*},
    ty::Type,
    ParamEnv,
};

/// An internal builder for lvalue lowering.
struct Builder<'a, C> {
    cx: &'a C,
    span: Span,
    expr: NodeId,
    env: ParamEnv,
}

impl<'a, C: Context<'a>> Builder<'_, C> {
    /// Create a new builder for a different node.
    #[allow(dead_code)]
    fn with(&self, expr: NodeId) -> Self {
        Builder {
            cx: self.cx,
            span: self.cx.span(expr),
            expr,
            env: self.env,
        }
    }

    /// Intern an MIR node.
    fn build(&self, ty: Type<'a>, kind: LvalueKind<'a>) -> &'a Lvalue<'a> {
        self.cx.arena().alloc_mir_lvalue(Lvalue {
            id: self.cx.alloc_id(self.span),
            origin: self.expr,
            env: self.env,
            span: self.span,
            ty,
            kind: kind,
        })
    }

    /// Create an error node.
    ///
    /// This is usually called when something goes wrong during MIR construction
    /// and a marker node is needed to indicate that part of the MIR is invalid.
    fn error(&self) -> &'a Lvalue<'a> {
        self.build(&ty::ERROR_TYPE, LvalueKind::Error)
    }
}

/// Lower an expression to an lvalue in the MIR.
pub fn lower_expr<'gcx>(
    cx: &impl Context<'gcx>,
    expr_id: NodeId,
    env: ParamEnv,
) -> &'gcx Lvalue<'gcx> {
    let span = cx.span(expr_id);
    let builder = Builder {
        cx,
        span,
        expr: expr_id,
        env,
    };
    try_lower_expr(&builder, expr_id).unwrap_or_else(|_| builder.error())
}

/// Lower an expression to an lvalue in the MIR.
///
/// May return an error if any of the database queries break.
fn try_lower_expr<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    expr_id: NodeId,
) -> Result<&'gcx Lvalue<'gcx>> {
    // Determine the expression type.
    let ty = builder.cx.type_of(expr_id, builder.env)?;

    // Try to extract the expr HIR for this node. Handle a few special cases
    // where the node is not technically an expression, but can be used as a
    // lvalue.
    let hir = match builder.cx.hir_of(expr_id)? {
        HirNode::Expr(x) => x,
        HirNode::VarDecl(decl) => return Ok(builder.build(ty, LvalueKind::Var(decl.id))),
        HirNode::Port(port) => return Ok(builder.build(ty, LvalueKind::Port(port.id))),
        x => unreachable!("lvalue for {:#?}", x),
    };

    // Match on the various forms.
    match hir.kind {
        // Identifiers and scoped identifiers we simply resolve and try to lower
        // the resolved node to an MIR node.
        hir::ExprKind::Ident(..) | hir::ExprKind::Scope(..) => {
            let binding = builder.cx.resolve_node(expr_id, builder.env)?;
            match builder.cx.hir_of(binding)? {
                HirNode::VarDecl(..) | HirNode::Port(..) => {
                    return try_lower_expr(builder, binding);
                }
                _ => (),
            }
        }

        hir::ExprKind::Index(target, mode) => {
            // Compute the indexing parameters.
            let (base, length) = compute_indexing(builder.cx, builder.expr, builder.env, mode)?;

            // Lower the indexee and make sure it can be indexed into.
            let target = lower_expr(builder.cx, target, builder.env);
            if !target.ty.is_array() && !target.ty.is_bit_vector() {
                builder.cx.emit(
                    DiagBuilder2::error(format!(
                        "`{}` cannot be index into",
                        target.span.extract()
                    ))
                    .span(target.span),
                );
                return Err(());
            };

            // Build the cast lvalue.
            return Ok(builder.build(
                ty,
                LvalueKind::Index {
                    value: target,
                    base,
                    length,
                },
            ));
        }

        hir::ExprKind::Field(target, _) => {
            let value = lower_expr(builder.cx, target, builder.env);
            let (_, field, _) = builder.cx.resolve_field_access(expr_id, builder.env)?;
            return Ok(builder.build(ty, LvalueKind::Member { value, field }));
        }

        _ => (),
    }

    // Show an error informing the user that the given expression cannot be
    // assigned to.
    error!("{:#?}", hir);
    builder.cx.emit(
        DiagBuilder2::error(format!("{} cannot be assigned to", hir.desc_full()))
            .span(builder.span),
    );
    Err(())
}
