// Copyright (c) 2016-2020 Fabian Schuiki

//! Expression lvalue lowering to MIR.

use crate::crate_prelude::*;
use crate::{
    hir::HirNode,
    mir::{lower::rvalue::compute_indexing, lvalue::*},
    syntax::ast::BasicNode,
    ty::{SbvType, UnpackedType},
    ParamEnv,
};
use num::ToPrimitive;

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
    fn build(&self, ty: &'a UnpackedType<'a>, kind: LvalueKind<'a>) -> &'a Lvalue<'a> {
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
        self.build(UnpackedType::make_error(), LvalueKind::Error)
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
    let cx = builder.cx;
    let span = builder.span;
    let env = builder.env;

    // Try to extract the expr HIR for this node. Handle a few special cases
    // where the node is not technically an expression, but can be used as a
    // lvalue.
    let hir = match cx.hir_of(expr_id) {
        Ok(HirNode::Expr(x)) => x,
        Ok(x) => bug_span!(span, cx, "no lvalue for {:?}", x),
        Err(_) => return Ok(builder.error()),
    };

    // Determine the expression type.
    let ty = cx.type_of_expr(Ref(hir), env);
    if ty.is_error() {
        return Ok(builder.error());
    }

    // Match on the various forms.
    match hir.kind {
        // Identifiers and scoped identifiers we simply resolve and try to lower
        // the resolved node to an MIR node.
        hir::ExprKind::Ident(..) | hir::ExprKind::Scope(..) => {
            let binding = cx.resolve_node(expr_id, env)?;
            return match cx.hir_of(binding)? {
                HirNode::GenvarDecl(decl) => Ok(builder.build(ty, LvalueKind::Genvar(decl.id))),
                HirNode::VarDecl(decl) => Ok(builder.build(ty, LvalueKind::Var(decl.id))),
                HirNode::IntPort(port) if ty.resolve_full().core.get_interface().is_some() => {
                    Ok(builder.build(ty, LvalueKind::Intf(port.id)))
                }
                HirNode::IntPort(port) => Ok(builder.build(ty, LvalueKind::Port(port.id))),
                HirNode::Inst(inst) if ty.resolve_full().core.get_interface().is_some() => {
                    Ok(builder.build(ty, LvalueKind::Intf(inst.id)))
                }
                x => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "{} cannot be used as the target of an assignment",
                            x.desc_full()
                        ))
                        .span(span),
                    );
                    Err(())
                }
            };
        }

        hir::ExprKind::Index(target, mode) => {
            // Compute the indexing parameters.
            let (base, length) = compute_indexing(cx, builder.expr, env, mode)?;

            // Lower the indexee and make sure it can be indexed into.
            let target = cx.mir_lvalue(target, env);
            assert_span!(
                target.ty.dims().next().is_some(),
                target.span,
                cx,
                "cannot index into `{}`; should be handled by typeck",
                target.ty
            );

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

        hir::ExprKind::Field(target, name) => {
            let target_ty = cx.self_determined_type(target, env);
            let value = cx.mir_lvalue(target, env);
            if let Some(intf) = target_ty.and_then(|ty| ty.get_interface()) {
                let def = cx.resolve_hierarchical_or_error(name, intf.ast)?;
                // Distinguish `intf.modport` and `intf.signal`.
                if def.node.as_all().is_modport_name() {
                    return Ok(builder.build(ty, value.kind.clone()));
                } else {
                    return Ok(builder.build(ty, LvalueKind::IntfSignal(value, def.node.id())));
                }
            } else {
                let (field, _) = cx.resolve_field_access(expr_id, env)?;
                return Ok(builder.build(ty, LvalueKind::Member { value, field }));
            }
        }

        hir::ExprKind::Concat(repeat, ref exprs) => {
            // Compute the SBVT for each expression and lower it to MIR,
            // implicitly casting to the SBVT.
            let exprs = exprs
                .iter()
                .map(|&expr| {
                    let value = builder.cx.mir_lvalue(expr, env);
                    assert_span!(value.ty.coalesces_to_llhd_scalar(), value.span, builder.cx);
                    Ok((value.ty.get_bit_size().unwrap(), value))
                })
                .collect::<Result<Vec<_>>>()?;

            // Compute the result type of the concatenation.
            let final_ty = builder.cx.need_self_determined_type(hir.id, env);
            if final_ty.is_error() {
                return Err(());
            }
            let domain = final_ty.domain();
            let concat_width = exprs.iter().map(|(w, _)| w).sum();
            let concat_ty =
                SbvType::new(domain, ty::Sign::Unsigned, concat_width).to_unpacked(builder.cx);

            // Assemble the concatenation.
            let concat = builder.build(
                concat_ty,
                LvalueKind::Concat(exprs.into_iter().map(|(_, v)| v).collect()),
            );

            // If a repetition is present, apply that.
            let repeat = if let Some(repeat) = repeat {
                let count = builder
                    .cx
                    .constant_int_value_of(repeat, env)?
                    .to_usize()
                    .unwrap();
                builder.build(final_ty, LvalueKind::Repeat(count, concat))
            } else {
                concat
            };
            return Ok(repeat);
        }

        _ => (),
    }

    // Show an error informing the user that the given expression cannot be
    // assigned to.
    error!("{:#?}", hir);
    cx.emit(DiagBuilder2::error(format!("{} cannot be assigned to", hir.desc_full())).span(span));
    Err(())
}
