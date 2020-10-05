// Copyright (c) 2016-2020 Fabian Schuiki

//! Expression lvalue lowering to MIR.

use crate::crate_prelude::*;
use crate::{
    hir::HirNode,
    mir::{
        lower,
        lower::rvalue::{adjust_indexing, compute_indexing},
        lvalue::*,
    },
    syntax::ast::BasicNode,
    ty::{SbvType, UnpackedType},
    typeck::{CastOp, CastType},
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
pub fn lower_expr<'a>(cx: &impl Context<'a>, expr_id: NodeId, env: ParamEnv) -> &'a Lvalue<'a> {
    let span = cx.span(expr_id);
    let builder = Builder {
        cx,
        span,
        expr: expr_id,
        env,
    };

    // Try to extract the expr HIR for this node. Handle a few special cases
    // where the node is not technically an expression, but can be used as a
    // lvalue.
    let hir = match cx.hir_of(expr_id) {
        Ok(HirNode::Expr(x)) => x,
        Ok(x) => bug_span!(span, cx, "no lvalue for {:?}", x),
        Err(_) => return builder.error(),
    };

    // Determine the cast type.
    let cast = cx.cast_type(expr_id, env).unwrap();

    // Lower the expression.
    let lvalue = lower_expr_inner(&builder, hir, cast.init).unwrap_or_else(|_| builder.error());
    if lvalue.is_error() {
        return lvalue;
    }
    assert_span!(
        lvalue.ty.is_identical(cast.init),
        hir.span,
        cx,
        "lvalue lowering produced type `{}`, expected `{}`",
        lvalue.ty,
        cast.init
    );

    // Lower the casts.
    lower_cast(&builder, lvalue, cast)
}

/// Lower an expression to an rvalue in the MIR.
///
/// May return an error if any of the database queries break.
fn lower_expr_inner<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    hir: &'a hir::Expr<'a>,
    ty: &'a UnpackedType<'a>,
) -> Result<&'a Lvalue<'a>> {
    let expr_id = hir.id;
    let cx = builder.cx;
    let span = cx.span(expr_id);
    let env = builder.env;
    if ty.is_error() {
        return Err(());
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

            // Offset the indexing base by the dimension base, e.g. for accesses
            // such as `x[1]` into `logic [2:1] x`, which essentially accesses
            // element 0.
            let target_dim = target.ty.dims().next().unwrap();
            let rvalue_builder = lower::rvalue::Builder {
                cx,
                span: base.span,
                expr: base.id,
                env: base.env,
            };
            let base = adjust_indexing(&rvalue_builder, base, target_dim);

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
                    assert_span!(
                        value.ty.coalesces_to_llhd_scalar(),
                        value.span,
                        builder.cx,
                        "type `{}` does not coalesce to LLHD scalar",
                        value.ty
                    );
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

/// Generate the nodes necessary for a cast operation.
fn lower_cast<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    mut value: &'a Lvalue<'a>,
    to: CastType<'a>,
) -> &'a Lvalue<'a> {
    // Don't bother with errors.
    if value.is_error() {
        return value;
    }
    if to.is_error() {
        return builder.error();
    }
    assert_type!(
        value.ty,
        to.init,
        value.span,
        builder.cx,
        "lvalue type `{}` does not match initial type of cast `{}`",
        value.ty,
        to
    );
    trace!(
        "Lowering cast to `{}` from `{}` of `{}` (line {})",
        to,
        value.ty,
        value.span.extract(),
        value.span.begin().human_line()
    );

    // Lower each cast individually.
    for &(op, to) in &to.casts {
        debug!("- {:?} from `{}` to `{}`", op, value.ty, to);
        match op {
            CastOp::PickModport => {
                value = builder.build(to, value.kind.clone());
            }
            _ => {
                bug_span!(
                    value.span,
                    builder.cx,
                    "lvalue lowering of cast to `{}` not yet supported: {:?}",
                    to,
                    op
                );
            }
        }
        if !value.ty.is_identical(to) {
            error!(
                "Cast {:?} should have produced `{}`, but value is `{}`",
                op, to, value.ty
            );
        }
    }

    // Check that the casts have actually produced the expected output type.
    assert_type!(
        value.ty,
        to.ty,
        value.span,
        builder.cx,
        "lvalue type `{}` does not match final cast type `{}` after lower_cast",
        value.ty,
        to.ty
    );
    value
}
