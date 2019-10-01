// Copyright (c) 2016-2019 Fabian Schuiki

//! Lowering to MIR.

use crate::{
    crate_prelude::*,
    hir::HirNode,
    hir::PatternMapping,
    mir::rvalue::*,
    ty::{Type, TypeKind},
    value::ValueKind,
    ParamEnv,
};
use num::ToPrimitive;
use std::collections::HashMap;

// TODO(fschuiki): The result of these functions should be interned into the
// context and the resulting reference should be thrown around as desired.

// TODO(fschuiki): Decide whether to create an rvalue lowering struct that keeps
// track of the current span/origin/parent/ty context and makes it easier to
// emit multiple mir nodes per hir expression.

// TODO(fschuiki): Maybe move most of the functions below into the rvalue mod?

struct Builder {
    span: Span,
    expr: NodeId,
    env: ParamEnv,
}

impl Builder {
    /// Intern an MIR node.
    fn build<'a>(
        &self,
        cx: &impl Context<'a>,
        ty: Type<'a>,
        kind: RvalueKind<'a>,
    ) -> &'a Rvalue<'a> {
        cx.arena().alloc_mir_rvalue(Rvalue {
            span: self.span,
            ty,
            kind: kind,
        })
    }

    /// Create an error node.
    ///
    /// This is usually called when something goes wrong during MIR construction
    /// and a marker node is needed to indicate that part of the MIR is invalid.
    fn error<'a>(&self, cx: &impl Context<'a>) -> &'a Rvalue<'a> {
        self.build(cx, cx.mkty_void(), RvalueKind::Error)
    }
}

/// Lower an expression to an rvalue in the MIR.
pub fn lower_expr_to_mir_rvalue<'gcx>(
    cx: &impl Context<'gcx>,
    expr_id: NodeId,
    env: ParamEnv,
) -> &'gcx Rvalue<'gcx> {
    let span = cx.span(expr_id);
    let builder = Builder {
        span,
        expr: expr_id,
        env,
    };
    let result = || -> Result<&Rvalue> {
        let hir = match cx.hir_of(expr_id)? {
            HirNode::Expr(x) => x,
            HirNode::VarDecl(decl) => unimplemented!("mir rvalue for {:?}", decl),
            HirNode::Port(port) => unimplemented!("mir rvalue for {:?}", port),
            x => unreachable!("rvalue for {:#?}", x),
        };
        let ty = cx.type_of(expr_id, env)?;
        match hir.kind {
            hir::ExprKind::IntConst(..)
            | hir::ExprKind::UnsizedConst(..)
            | hir::ExprKind::TimeConst(_) => {
                let k = cx.constant_value_of(expr_id, env)?;
                trace!("const mir node for {:?}", k);
                Ok(builder.build(cx, k.ty, RvalueKind::Error))
            }
            // hir::ExprKind::Ident(name) => {
            //     let binding = cx.resolve_node(expr_id, env)?;
            //     if cx.is_constant(binding)? {
            //         let k = cx.constant_value_of(binding, env)?;
            //         // TODO: Map to const
            //         return Err(());
            //     }
            //     // TODO: Check what the binding actually is and emit a node.
            //     Err(())
            // }
            hir::ExprKind::NamedPattern(ref mapping) => {
                if ty.is_array() {
                    Ok(lower_array_pattern(cx, &builder, mapping, ty))
                } else if ty.is_struct() {
                    Ok(builder.build(cx, ty, lower_struct_pattern(cx, mapping)))
                } else {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "`'{{...}}` cannot construct a value of type {}",
                            ty
                        ))
                        .span(span),
                    );
                    Err(())
                }
            }
            _ => unreachable!("lowering to mir rvalue of {:?}", hir),
        }
    }();
    result.unwrap_or_else(|_| builder.error(cx))
}

fn lower_expr_and_cast<'gcx>(
    cx: &impl Context<'gcx>,
    expr_id: NodeId,
    env: ParamEnv,
    target_ty: Type<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    let inner = lower_expr_to_mir_rvalue(cx, expr_id, env);
    let builder = Builder {
        span: inner.span,
        expr: expr_id,
        env,
    };
    lower_implicit_cast(cx, &builder, inner, target_ty)
}

/// Generate the nodes necessary to implicitly cast and rvalue to a type.
///
/// If the cast is not possible, emit some helpful diagnostics.
fn lower_implicit_cast<'gcx>(
    cx: &impl Context<'gcx>,
    builder: &Builder,
    value: &'gcx Rvalue<'gcx>,
    to: Type<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    let from = value.ty;

    // Catch the easy case where the types already line up.
    if from == to {
        return value;
    }

    // Strip away all named types.
    let from_raw = from.resolve_name();
    let to_raw = to.resolve_name();
    trace!(
        "trying implicit cast {:?} from {:?} to {:?}",
        value,
        from_raw,
        to_raw
    );

    // Try to make the cast happen.
    match (from_raw, to_raw) {
        // Integer domain transfer; e.g. `int` to `integer`.
        (&TypeKind::Int(fw, fd), &TypeKind::Int(_, td))
        | (&TypeKind::Int(fw, fd), &TypeKind::Bit(td))
            if fd != td =>
        {
            // trace!("int domain transfer {:?} to {:?}", fd, td);
            let inner = builder.build(
                cx,
                cx.intern_type(TypeKind::Int(fw, td)),
                RvalueKind::CastValueDomain {
                    from: fd,
                    to: td,
                    value,
                },
            );
            return lower_implicit_cast(cx, builder, inner, to);
        }

        // Bit domain transfer; e.g. `bit` to `logic`.
        (&TypeKind::Bit(fd), &TypeKind::Int(_, td)) | (&TypeKind::Bit(fd), &TypeKind::Bit(td))
            if fd != td =>
        {
            // trace!("bit domain transfer {:?} to {:?}", fd, td);
            let inner = builder.build(
                cx,
                cx.intern_type(TypeKind::Bit(td)),
                RvalueKind::CastValueDomain {
                    from: fd,
                    to: td,
                    value,
                },
            );
            return lower_implicit_cast(cx, builder, inner, to);
        }

        // Integer to bit truncation; e.g. `int` to `bit`.
        (&TypeKind::Int(fw, fd), &TypeKind::Bit(_)) if fw > 1 => {
            // trace!("would narrow {} int to 1 bit", fw);
            let inner = builder.build(
                cx,
                cx.intern_type(TypeKind::Int(1, fd)),
                RvalueKind::Truncate {
                    target_width: 1,
                    value,
                },
            );
            return lower_implicit_cast(cx, builder, inner, to);
        }

        // Integer to bit conversion; e.g. `bit [0:0]` to `bit`.
        (&TypeKind::Int(fw, fd), &TypeKind::Bit(_)) if fw == 1 => {
            // trace!("would map int to bit");
            let inner = builder.build(
                cx,
                cx.intern_type(TypeKind::Bit(fd)),
                RvalueKind::CastVectorToAtom { domain: fd, value },
            );
            return lower_implicit_cast(cx, builder, inner, to);
        }

        // TODO(fschuiki): Packing structs into bit vectors.
        // TODO(fschuiki): Unpacking structs from bit vectors.
        // TODO(fschuiki): Integer truncation.
        // TODO(fschuiki): Integer extension.
        // TODO(fschuiki): Array truncation.
        // TODO(fschuiki): Array extension.
        // TODO(fschuiki): Signed/unsigned conversion.
        _ => (),
    }

    // Complain and abort.
    cx.emit(
        DiagBuilder2::error(format!(
            "type `{}` required, but expression has type `{}`",
            to, from
        ))
        .span(value.span),
    );
    builder.error(cx)
}

/// Lower an `'{...}` array pattern.
fn lower_array_pattern<'gcx>(
    cx: &impl Context<'gcx>,
    builder: &Builder,
    mapping: &[(PatternMapping, NodeId)],
    ty: Type<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    let length = ty.get_array_length().unwrap();
    let elem_ty = ty.get_array_element().unwrap();
    let mut failed = false;
    let mut default: Option<&Rvalue> = None;
    let mut values = HashMap::<usize, &Rvalue>::new();
    for &(map, to) in mapping {
        match map {
            PatternMapping::Type(type_id) => {
                cx.emit(
                    DiagBuilder2::error("types cannot index into an array").span(cx.span(type_id)),
                );
                failed = true;
                continue;
            }
            PatternMapping::Member(member_id) => {
                // Determine the index for the mapping.
                let index = match || -> Result<usize> {
                    let index = cx.constant_value_of(member_id, builder.env)?;
                    let index = match &index.kind {
                        ValueKind::Int(i) => i,
                        _ => {
                            cx.emit(
                                DiagBuilder2::error("array index must be a constant integer")
                                    .span(cx.span(member_id)),
                            );
                            return Err(());
                        }
                    };
                    let index = match index.to_usize() {
                        Some(i) if i < length => i,
                        _ => {
                            cx.emit(
                                DiagBuilder2::error(format!("index `{}` out of bounds", index))
                                    .span(cx.span(member_id)),
                            );
                            return Err(());
                        }
                    };
                    Ok(index)
                }() {
                    Ok(i) => i,
                    Err(_) => {
                        failed = true;
                        continue;
                    }
                };

                // Determine the value and insert into the mappings.
                let value = lower_expr_and_cast(cx, to, builder.env, elem_ty);
                let span = value.span;
                if let Some(prev) = values.insert(index, value) {
                    cx.emit(
                        DiagBuilder2::warning(format!(
                            "`{}` overwrites previous value `{}` at index {}",
                            span.extract(),
                            prev.span.extract(),
                            index
                        ))
                        .span(span)
                        .add_note("Previous value was here:")
                        .span(prev.span),
                    );
                }
            }
            PatternMapping::Default => match default {
                Some(ref default) => {
                    cx.emit(
                        DiagBuilder2::error("pattern has multiple default mappings")
                            .span(cx.span(to))
                            .add_note("Previous mapping default mapping was here:")
                            .span(default.span),
                    );
                    failed = true;
                    continue;
                }
                None => {
                    default = Some(lower_expr_and_cast(cx, to, builder.env, elem_ty));
                }
            },
        }
    }

    // In case the list of indices provided by the user is incomplete, use the
    // default to fill in the other elements.
    if values.len() != length {
        let default = if let Some(default) = default {
            default
        } else {
            cx.emit(
                DiagBuilder2::error("`default:` missing in non-exhaustive array pattern")
                    .span(builder.span)
                    .add_note("Array patterns must assign a value to every index."),
            );
            return builder.error(cx);
        };
        for i in 0..length {
            if values.contains_key(&i) {
                continue;
            }
            values.insert(i, default);
        }
    }

    if failed {
        builder.error(cx)
    } else {
        builder.build(
            cx,
            cx.mkty_packed_array(length, elem_ty),
            RvalueKind::ConstructArray(values),
        )
    }
}

fn lower_struct_pattern<'gcx>(
    cx: &impl Context<'gcx>,
    mapping: &[(PatternMapping, NodeId)],
) -> RvalueKind<'gcx> {
    error!("missing struct pattern");
    RvalueKind::Error
}
