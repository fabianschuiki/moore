// Copyright (c) 2016-2019 Fabian Schuiki

//! Expression rvalue lowering to MIR.

use crate::{
    common::{SessionContext, Verbosity},
    crate_prelude::*,
    hir::HirNode,
    hir::PatternMapping,
    mir::rvalue::*,
    ty::{Type, TypeKind},
    value::ValueKind,
    ParamEnv,
};
use num::{BigInt, One, Signed, ToPrimitive};
use std::{cmp::max, collections::HashMap};

/// An internal builder for rvalue lowering.
struct Builder<'a, C> {
    cx: &'a C,
    span: Span,
    expr: NodeId,
    env: ParamEnv,
}

impl<'a, C: Context<'a>> Builder<'_, C> {
    /// Create a new builder for a different node.
    fn with(&self, expr: NodeId) -> Self {
        Builder {
            cx: self.cx,
            span: self.cx.span(expr),
            expr,
            env: self.env,
        }
    }

    /// Intern an MIR node.
    fn build(&self, ty: Type<'a>, kind: RvalueKind<'a>) -> &'a Rvalue<'a> {
        self.cx.arena().alloc_mir_rvalue(Rvalue {
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
    fn error(&self) -> &'a Rvalue<'a> {
        self.build(&ty::ERROR_TYPE, RvalueKind::Error)
    }
}

/// Lower an expression to an rvalue in the MIR.
pub fn lower_expr<'gcx>(
    cx: &impl Context<'gcx>,
    expr_id: NodeId,
    env: ParamEnv,
) -> &'gcx Rvalue<'gcx> {
    let span = cx.span(expr_id);
    let builder = Builder {
        cx,
        span,
        expr: expr_id,
        env,
    };
    try_lower_expr(&builder, expr_id).unwrap_or_else(|_| builder.error())
}

/// Lower an expression to an rvalue in the MIR.
///
/// May return an error if any of the database queries break.
fn try_lower_expr<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    expr_id: NodeId,
) -> Result<&'gcx Rvalue<'gcx>> {
    let cx = builder.cx;
    let span = cx.span(expr_id);
    let env = builder.env;

    // Check whether the node has a constant value. This will allow us to
    // quickly emit parameters and genvars.
    let is_const = builder.cx.is_constant(expr_id).unwrap_or(false);

    // Try to extract the expr HIR for this node. Handle a few special cases
    // where the node is not technically an expression, but can be used as a
    // rvalue.
    let hir = match builder.cx.hir_of(expr_id)? {
        HirNode::Expr(x) => x,
        HirNode::VarDecl(decl) => {
            return Ok(builder.build(builder.cx.type_of(expr_id, env)?, RvalueKind::Var(decl.id)))
        }
        HirNode::Port(port) => {
            return Ok(builder.build(builder.cx.type_of(expr_id, env)?, RvalueKind::Port(port.id)))
        }
        HirNode::EnumVariant(..) => {
            let k = builder.cx.constant_value_of(expr_id, env)?;
            return Ok(builder.build(k.ty, RvalueKind::Const(k)));
        }
        _ if is_const => {
            let k = builder.cx.constant_value_of(expr_id, env)?;
            return Ok(builder.build(k.ty, RvalueKind::Const(k)));
        }
        x => unreachable!("rvalue for {:#?}", x),
    };

    // Determine the expression type and match on the various forms.
    let ty = builder.cx.type_of(expr_id, env)?;
    match hir.kind {
        hir::ExprKind::IntConst(..)
        | hir::ExprKind::UnsizedConst(..)
        | hir::ExprKind::TimeConst(_)
        | hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(_))
        | hir::ExprKind::Builtin(hir::BuiltinCall::Bits(_)) => {
            let k = builder.cx.constant_value_of(expr_id, env)?;
            Ok(builder.build(k.ty, RvalueKind::Const(k)))
        }
        hir::ExprKind::Ident(..) | hir::ExprKind::Scope(..) => {
            let binding = builder.cx.resolve_node(expr_id, env)?;
            match builder.cx.hir_of(binding)? {
                HirNode::VarDecl(..)
                | HirNode::Port(..)
                | HirNode::EnumVariant(..)
                | HirNode::ValueParam(..)
                | HirNode::GenvarDecl(..) => try_lower_expr(builder, binding),
                x => {
                    builder.cx.emit(
                        DiagBuilder2::error(format!(
                            "{} cannot be used in expression",
                            x.desc_full()
                        ))
                        .span(span),
                    );
                    Err(())
                }
            }
        }
        hir::ExprKind::Unary(op, arg) => Ok(lower_unary(&builder, ty, op, arg)),
        hir::ExprKind::Binary(op, lhs, rhs) => Ok(lower_binary(&builder, ty, op, lhs, rhs)),
        hir::ExprKind::Ternary(cond, true_value, false_value) => {
            let cond = {
                let subbuilder = Builder {
                    cx,
                    span: cx.span(cond),
                    expr: cond,
                    env,
                };
                implicit_cast_to_bool(&subbuilder, lower_expr(subbuilder.cx, cond, subbuilder.env))
            };
            let true_value = lower_expr_and_cast(cx, true_value, env, ty);
            let false_value = lower_expr_and_cast(cx, false_value, env, ty);
            Ok(builder.build(
                ty,
                RvalueKind::Ternary {
                    cond,
                    true_value,
                    false_value,
                },
            ))
        }
        hir::ExprKind::NamedPattern(ref mapping) => {
            if ty.is_array() || ty.is_bit_vector() {
                Ok(lower_array_pattern(&builder, mapping, ty))
            } else if ty.is_struct() {
                Ok(lower_struct_pattern(&builder, mapping, ty))
            } else {
                builder.cx.emit(
                    DiagBuilder2::error(format!(
                        "`'{{...}}` cannot construct a value of type {}",
                        ty
                    ))
                    .span(span),
                );
                Err(())
            }
        }
        hir::ExprKind::Concat(repeat, ref exprs) => {
            // Compute the SBVT for each expression and lower it to MIR,
            // implicitly casting to the SBVT.
            let exprs = exprs
                .iter()
                .map(|&expr| {
                    let ty = builder.cx.type_of(expr, env)?;
                    let flat_ty = match map_to_simple_bit_type(builder.cx, ty, env) {
                        Some(ty) => ty,
                        None => {
                            builder.cx.emit(
                                DiagBuilder2::error(format!(
                                    "`{}` cannot be used in concatenation",
                                    ty
                                ))
                                .span(builder.cx.span(expr)),
                            );
                            return Err(());
                        }
                    };
                    Ok((
                        ty::bit_size_of_type(builder.cx, ty, env)?,
                        lower_expr_and_cast(builder.cx, expr, env, flat_ty),
                    ))
                })
                .collect::<Result<Vec<_>>>()?;

            // Compute the result type of the concatenation.
            let total_width = exprs.iter().map(|(w, _)| w).sum();
            let result_ty = builder.cx.intern_type(TypeKind::BitVector {
                domain: ty::Domain::FourValued, // TODO(fschuiki): check if this is correct
                sign: ty::Sign::Unsigned,       // fixed by standard
                range: ty::Range {
                    size: total_width,
                    dir: ty::RangeDir::Down,
                    offset: 0isize,
                },
                dubbed: false,
            });

            // Assemble the concatenation.
            let concat = builder.build(
                result_ty,
                RvalueKind::Concat(exprs.into_iter().map(|(_, v)| v).collect()),
            );

            // If a repetition is present, apply that.
            let repeat = if let Some(repeat) = repeat {
                let count = builder
                    .cx
                    .constant_int_value_of(repeat, env)?
                    .to_usize()
                    .unwrap();
                let total_width = total_width * count;
                let result_ty = builder.cx.intern_type(TypeKind::BitVector {
                    domain: ty::Domain::FourValued,
                    sign: ty::Sign::Unsigned,
                    range: ty::Range {
                        size: total_width,
                        dir: ty::RangeDir::Down,
                        offset: 0isize,
                    },
                    dubbed: false,
                });
                builder.build(result_ty, RvalueKind::Repeat(count, concat))
            } else {
                concat
            };
            Ok(repeat)
        }

        hir::ExprKind::Builtin(hir::BuiltinCall::Signed(id)) => {
            Ok(lower_expr_and_cast_sign(&builder, id, ty::Sign::Signed))
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::Unsigned(id)) => {
            Ok(lower_expr_and_cast_sign(&builder, id, ty::Sign::Unsigned))
        }

        hir::ExprKind::Index(target, mode) => {
            let (base, length) = compute_indexing(cx, builder.expr, env, mode)?;

            // Cast the target to a simple bit vector type if needed.
            let target_ty = cx.type_of(target, env)?;
            let target = if target_ty.is_array() {
                // No need to cast arrays.
                lower_expr(cx, target, env)
            } else {
                let sbvt = match map_to_simple_bit_vector_type(cx, target_ty, env) {
                    Some(ty) => ty,
                    None => {
                        let span = builder.cx.span(target);
                        builder.cx.emit(
                            DiagBuilder2::error(format!(
                                "`{}` cannot be index into",
                                span.extract()
                            ))
                            .span(span)
                            .add_note(format!(
                                "`{}` cannot has no simple bit-vector type representation",
                                target_ty
                            )),
                        );
                        return Ok(builder.error());
                    }
                };
                lower_expr_and_cast(cx, target, env, sbvt)
            };

            // Build the cast rvalue.
            Ok(builder.build(
                ty,
                RvalueKind::Index {
                    value: target,
                    base,
                    length,
                },
            ))
        }

        hir::ExprKind::Field(target, _) => {
            let value = lower_expr(cx, target, env);
            let (_, field, _) = cx.resolve_field_access(expr_id, env)?;
            Ok(builder.build(ty, RvalueKind::Member { value, field }))
        }

        hir::ExprKind::Cast(ty, expr) => {
            let ty = cx.type_of(ty, env)?;
            Ok(lower_expr_and_cast(cx, expr, env, ty))
        }

        _ => {
            error!("{:#?}", hir);
            cx.unimp_msg("lowering to mir rvalue of", hir)
        }
    }
}

/// Compute the base and length of an indexing operation.
///
/// Determine the index of the LSB and the width of the selection. Note that
/// bit-selects are mapped to part-selects of length 0.
pub(crate) fn compute_indexing<'gcx>(
    cx: &impl Context<'gcx>,
    origin: NodeId,
    env: ParamEnv,
    mode: hir::IndexMode,
) -> Result<(&'gcx Rvalue<'gcx>, usize)> {
    let builder = Builder {
        cx,
        span: cx.span(origin),
        expr: origin,
        env,
    };
    Ok(match mode {
        hir::IndexMode::One(index) => (lower_expr(cx, index, env), 0),
        hir::IndexMode::Many(ast::RangeMode::RelativeUp, base, delta) => (
            lower_expr(cx, base, env),
            builder
                .cx
                .constant_int_value_of(delta, env)?
                .to_usize()
                .unwrap(),
        ),
        hir::IndexMode::Many(ast::RangeMode::RelativeDown, base, delta) => {
            let base = lower_expr(cx, base, env);
            let delta_rvalue = lower_expr_and_cast(cx, delta, env, base.ty);
            let base = builder.build(
                base.ty,
                RvalueKind::IntBinaryArith {
                    op: IntBinaryArithOp::Sub,
                    sign: base.ty.get_sign().unwrap(),
                    domain: base.ty.get_value_domain().unwrap(),
                    lhs: base,
                    rhs: delta_rvalue,
                },
            );
            let length = builder
                .cx
                .constant_int_value_of(delta, env)?
                .to_usize()
                .unwrap();
            (base, length)
        }
        hir::IndexMode::Many(ast::RangeMode::Absolute, lhs, rhs) => {
            let lhs_int = cx.constant_int_value_of(lhs, env)?;
            let rhs_int = cx.constant_int_value_of(rhs, env)?;
            let base = std::cmp::min(lhs_int, rhs_int).clone();
            let base_ty = cx.mkty_int(max(base.bits(), 1));
            let base = cx.intern_value(value::make_int(base_ty, base));
            let base = builder.build(base_ty, RvalueKind::Const(base));
            let length = ((lhs_int - rhs_int).abs() + BigInt::one())
                .to_usize()
                .unwrap();
            (base, length)
        }
    })
}

/// Lower an HIR expression and implicitly cast to a target type.
fn lower_expr_and_cast<'gcx>(
    cx: &impl Context<'gcx>,
    expr_id: NodeId,
    env: ParamEnv,
    target_ty: Type<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    let inner = lower_expr(cx, expr_id, env);
    let builder = Builder {
        cx,
        span: inner.span,
        expr: expr_id,
        env,
    };
    lower_implicit_cast(&builder, inner, target_ty)
}

/// Lower an HIR expression and implicitly cast to a different sign.
fn lower_expr_and_cast_sign<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    expr_id: NodeId,
    sign: ty::Sign,
) -> &'gcx Rvalue<'gcx> {
    let inner = lower_expr(builder.cx, expr_id, builder.env);
    if let Some(ty) = map_to_simple_bit_type(builder.cx, inner.ty.resolve_name(), builder.env) {
        let ty = change_type_sign(builder.cx, ty, sign);
        lower_implicit_cast(builder, inner, ty)
    } else {
        let span = builder.cx.span(expr_id);
        builder.cx.emit(
            DiagBuilder2::error(format!("`{}` cannot be sign-cast", span.extract())).span(span),
        );
        builder.error()
    }
}

/// Generate the nodes necessary to implicitly cast and rvalue to a type.
///
/// If the cast is not possible, emit some helpful diagnostics.
fn lower_implicit_cast<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    value: &'gcx Rvalue<'gcx>,
    to: Type<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    let from = value.ty;
    let verbose = builder.cx.sess().has_verbosity(Verbosity::CASTS);

    // Catch the easy case where the types already line up.
    if ty::identical(from, to) || value.kind.is_error() || from.is_error() || to.is_error() {
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

    // Try a truncation or extension cast.
    let from_sbvt = map_to_simple_bit_vector_type(builder.cx, from_raw, builder.env);
    let to_sbvt = map_to_simple_bit_vector_type(builder.cx, to_raw, builder.env);
    let from_size = from_sbvt.map(|ty| ty.width());
    let to_size = to_sbvt.map(|ty| ty.width());

    if from_size.is_some() && to_size.is_some() && from_size != to_size {
        let from_sbvt = from_sbvt.unwrap();
        let value = lower_implicit_cast(builder, value, from_sbvt);
        let from_size = from_size.unwrap();
        let to_size = to_size.unwrap();
        let range = match *to_sbvt.unwrap() {
            TypeKind::BitVector { range, .. } => range,
            _ => unreachable!(),
        };
        let sign = from_sbvt.get_sign().unwrap();
        let ty = builder.cx.intern_type(TypeKind::BitVector {
            domain: from_sbvt.get_value_domain().unwrap(),
            sign,
            range,
            dubbed: false,
        });
        let kind = if from_size < to_size {
            match sign {
                ty::Sign::Signed => RvalueKind::SignExtend(range.size, value),
                ty::Sign::Unsigned => RvalueKind::ZeroExtend(range.size, value),
            }
        } else {
            RvalueKind::Truncate(range.size, value)
        };
        let inner = builder.build(ty, kind);
        if verbose {
            builder.cx.emit(
                DiagBuilder2::note(format!(
                    "cast size from {:?} to {:?}, {:?}",
                    from_size, to_size, sign
                ))
                .span(builder.span)
                .add_note(format!(
                    "from `{}` to `{}`; eventually `{}`",
                    from_raw, inner.ty, to
                )),
            );
        }
        return lower_implicit_cast(builder, inner, to);
    }

    // Try a single-bit atom/vector conversion.
    let from_sbt = map_to_simple_bit_type(builder.cx, from_raw, builder.env);
    let to_sbt = map_to_simple_bit_type(builder.cx, to_raw, builder.env);
    match (from_sbt, to_sbt) {
        (
            Some(&TypeKind::BitVector {
                domain,
                sign,
                range: ty::Range { size: 1, .. },
                ..
            }),
            Some(&TypeKind::BitScalar { .. }),
        ) => {
            let value = lower_implicit_cast(builder, value, from_sbt.unwrap());
            let inner = builder.build(
                builder.cx.intern_type(TypeKind::BitScalar { domain, sign }),
                RvalueKind::CastVectorToAtom { domain, value },
            );
            if verbose {
                builder.cx.emit(
                    DiagBuilder2::note("cast vector to atom")
                        .span(builder.span)
                        .add_note(format!(
                            "from `{}` to `{}`; eventually `{}`",
                            from_raw, inner.ty, to
                        )),
                );
            }
            return lower_implicit_cast(builder, inner, to);
        }
        (Some(&TypeKind::BitScalar { domain, sign }), Some(&TypeKind::BitVector { .. })) => {
            let value = lower_implicit_cast(builder, value, from_sbt.unwrap());
            let inner = builder.build(
                builder.cx.intern_type(TypeKind::BitVector {
                    domain,
                    sign,
                    range: ty::Range {
                        size: 1,
                        dir: ty::RangeDir::Down,
                        offset: 0isize,
                    },
                    dubbed: false,
                }),
                RvalueKind::CastAtomToVector { domain, value },
            );
            if verbose {
                builder.cx.emit(
                    DiagBuilder2::note("cast atom to vector")
                        .span(builder.span)
                        .add_note(format!(
                            "from `{}` to `{}`; eventually `{}`",
                            from_raw, inner.ty, to
                        )),
                );
            }
            return lower_implicit_cast(builder, inner, to);
        }
        _ => (),
    }

    // Try a value domain cast.
    let from_domain = from_raw.get_value_domain();
    let to_domain = to_raw.get_value_domain();
    if from_domain.is_some() && to_domain.is_some() && from_domain != to_domain {
        let fd = from_domain.unwrap();
        let td = to_domain.unwrap();
        let target_ty = match *from_raw {
            TypeKind::Bit(_) => builder.cx.intern_type(TypeKind::Bit(td)),
            TypeKind::Int(w, _) => builder.cx.intern_type(TypeKind::Int(w, td)),
            TypeKind::BitScalar { sign, .. } => builder
                .cx
                .intern_type(TypeKind::BitScalar { domain: td, sign }),
            TypeKind::BitVector {
                sign,
                range,
                dubbed,
                ..
            } => builder.cx.intern_type(TypeKind::BitVector {
                domain: td,
                sign,
                range,
                dubbed,
            }),
            _ => unreachable!(),
        };
        let inner = builder.build(
            target_ty,
            RvalueKind::CastValueDomain {
                from: fd,
                to: td,
                value,
            },
        );
        if verbose {
            builder.cx.emit(
                DiagBuilder2::note(format!("cast from {:?} to {:?}", fd, td))
                    .span(builder.span)
                    .add_note(format!(
                        "from `{}` to `{}`; eventually `{}`",
                        from_raw, inner.ty, to
                    )),
            );
        }
        return lower_implicit_cast(builder, inner, to);
    }

    // Try a sign cast.
    let from_sign = from_sbt.and_then(|ty| ty.get_sign());
    let to_sign = to_sbt.and_then(|ty| ty.get_sign());
    if from_sign.is_some() && to_sign.is_some() && from_sign != to_sign {
        let value = lower_implicit_cast(builder, value, from_sbt.unwrap());
        let ty = change_type_sign(builder.cx, from_sbt.unwrap(), to_sign.unwrap());
        let inner = builder.build(ty, RvalueKind::CastSign(to_sign.unwrap(), value));
        if verbose {
            builder.cx.emit(
                DiagBuilder2::note(format!(
                    "cast sign from {:?} to {:?}",
                    from_sign.unwrap(),
                    to_sign.unwrap()
                ))
                .span(builder.span)
                .add_note(format!(
                    "from `{}` to `{}`; eventually `{}`",
                    from_raw, inner.ty, to
                )),
            );
        }
        return lower_implicit_cast(builder, inner, to);
    }

    // Try struct/array packing.
    let packed = if from_raw.is_struct() {
        Some(pack_struct(builder, value))
    } else if from_raw.is_array() {
        Some(pack_array(builder, value))
    } else {
        None
    };
    if let Some(packed) = packed {
        if verbose {
            builder.cx.emit(
                DiagBuilder2::note("implicit cast: struct/array packing")
                    .span(builder.span)
                    .add_note(format!(
                        "from `{}` to `{}`; eventually `{}`",
                        from_raw, packed.ty, to
                    )),
            );
        }
        return lower_implicit_cast(builder, packed, to);
    }

    // Complain and abort.
    error!("failed implicit cast from {:?} to {:?}", from, to);
    info!("failed implicit cast from {:?}", value);
    builder.cx.emit(
        DiagBuilder2::error(format!(
            "type `{}` required, but expression has type `{}`",
            to, from
        ))
        .span(value.span),
    );
    builder.error()
}

/// Change the sign of a simple bit type.
fn change_type_sign<'gcx>(cx: &impl Context<'gcx>, ty: Type<'gcx>, sign: ty::Sign) -> Type<'gcx> {
    match *ty {
        TypeKind::BitScalar { domain, .. } => cx.intern_type(TypeKind::BitScalar { domain, sign }),
        TypeKind::BitVector {
            domain,
            range,
            dubbed,
            ..
        } => cx.intern_type(TypeKind::BitVector {
            domain,
            sign,
            range,
            dubbed,
        }),
        _ => ty,
    }
}

/// Pack a struct as a simple bit vector.
fn pack_struct<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    value: &'gcx Rvalue<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    let mut failed = false;

    // Get the field names and types.
    let def_id = value.ty.get_struct_def().unwrap();
    let def = match builder.cx.struct_def(def_id) {
        Ok(d) => d,
        Err(()) => return builder.error(),
    };

    // Pack each of the fields.
    let mut packed_fields = vec![];
    for (i, field) in def.fields.iter().enumerate() {
        let field_ty = match builder.cx.map_to_type(field.ty, builder.env) {
            Ok(t) => t,
            Err(()) => {
                failed = true;
                continue;
            }
        };
        let sbvt = map_to_simple_bit_vector_type(builder.cx, field_ty, builder.env);
        let sbvt = match sbvt {
            Some(x) => x,
            None => {
                builder.cx.emit(
                    DiagBuilder2::error(format!(
                        "field `{}` cannot be cast to a simple bit vector",
                        field.name
                    ))
                    .span(builder.span),
                );
                continue;
            }
        };
        let field_value = builder.build(field_ty, RvalueKind::Member { value, field: i });
        let field_value = lower_implicit_cast(builder, field_value, sbvt);
        packed_fields.push(field_value);
    }

    // Concatenate the fields.
    if failed {
        builder.error()
    } else {
        let ty = map_to_simple_bit_vector_type(builder.cx, value.ty, builder.env)
            .expect("struct must have sbvt");
        builder.build(ty, RvalueKind::Concat(packed_fields))
    }
}

/// Pack an array as a simple bit vector.
fn pack_array<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    value: &'gcx Rvalue<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    // Unpack the outermost array dimension.
    let length = value.ty.get_array_length().expect("array length");

    // Map the element type to its simple bit vector equivalent.
    let elem_ty = value.ty.get_array_element().expect("array element type");
    let sbvt = match map_to_simple_bit_vector_type(builder.cx, elem_ty, builder.env) {
        Some(x) => x,
        None => {
            builder.cx.emit(
                DiagBuilder2::error(format!(
                    "element type `{}` cannot be cast to a simple bit vector",
                    elem_ty
                ))
                .span(builder.span),
            );
            return builder.error();
        }
    };

    // Cast each element.
    let mut packed_elements = vec![];
    for i in 0..length {
        let i = builder.build(
            &ty::INT_TYPE,
            RvalueKind::Const(
                builder
                    .cx
                    .intern_value(value::make_int(&ty::INT_TYPE, i.into())),
            ),
        );
        let elem = builder.build(
            elem_ty,
            RvalueKind::Index {
                value,
                base: i,
                length: 0,
            },
        );
        let elem = lower_implicit_cast(builder, elem, sbvt);
        packed_elements.push(elem);
    }

    // Concatenate the elements.
    let ty = map_to_simple_bit_vector_type(builder.cx, value.ty, builder.env)
        .expect("array must have sbvt");
    builder.build(ty, RvalueKind::Concat(packed_elements))
}

/// Lower a `'{...}` array pattern.
fn lower_array_pattern<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    mapping: &[(PatternMapping, NodeId)],
    ty: Type<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    let (length, offset, elem_ty) = match *ty {
        TypeKind::PackedArray(w, t) => (w, 0isize, t),
        TypeKind::BitScalar { domain, .. } => (1, 0isize, domain.bit_type()),
        TypeKind::BitVector { domain, range, .. } => (range.size, range.offset, domain.bit_type()),
        _ => unreachable!("array pattern with invalid input type"),
    };
    let mut failed = false;
    let mut default: Option<&Rvalue> = None;
    let mut values = HashMap::<usize, &Rvalue>::new();
    for &(map, to) in mapping {
        match map {
            PatternMapping::Type(type_id) => {
                builder.cx.emit(
                    DiagBuilder2::error("types cannot index into an array")
                        .span(builder.cx.span(type_id)),
                );
                failed = true;
                continue;
            }
            PatternMapping::Member(member_id) => {
                // Determine the index for the mapping.
                let index = match || -> Result<usize> {
                    let index = builder.cx.constant_value_of(member_id, builder.env)?;
                    let index = match &index.kind {
                        ValueKind::Int(i) => i - num::BigInt::from(offset),
                        _ => {
                            builder.cx.emit(
                                DiagBuilder2::error("array index must be a constant integer")
                                    .span(builder.cx.span(member_id)),
                            );
                            return Err(());
                        }
                    };
                    let index = match index.to_isize() {
                        Some(i) if i >= 0 && i < length as isize => i as usize,
                        _ => {
                            builder.cx.emit(
                                DiagBuilder2::error(format!("index `{}` out of bounds", index))
                                    .span(builder.cx.span(member_id)),
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
                let value = lower_expr_and_cast(builder.cx, to, builder.env, elem_ty);
                let span = value.span;
                if let Some(prev) = values.insert(index, value) {
                    builder.cx.emit(
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
                    builder.cx.emit(
                        DiagBuilder2::error("pattern has multiple default mappings")
                            .span(builder.cx.span(to))
                            .add_note("Previous mapping default mapping was here:")
                            .span(default.span),
                    );
                    failed = true;
                    continue;
                }
                None => {
                    default = Some(lower_expr_and_cast(builder.cx, to, builder.env, elem_ty));
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
            builder.cx.emit(
                DiagBuilder2::error("`default:` missing in non-exhaustive array pattern")
                    .span(builder.span)
                    .add_note("Array patterns must assign a value to every index."),
            );
            return builder.error();
        };
        for i in 0..length {
            if values.contains_key(&i) {
                continue;
            }
            values.insert(i, default);
        }
    }

    match *ty {
        _ if failed => builder.error(),
        TypeKind::PackedArray(..) => builder.build(ty, RvalueKind::ConstructArray(values)),
        TypeKind::BitScalar { .. } => {
            assert_eq!(values.len(), 1);
            values[&0]
        }
        TypeKind::BitVector { .. } => builder.build(
            ty,
            RvalueKind::Concat((0..length).rev().map(|i| values[&i]).collect()),
        ),
        _ => unreachable!("array pattern with invalid input type"),
    }
}

/// Lower a `'{...}` struct pattern.
fn lower_struct_pattern<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    mapping: &[(PatternMapping, NodeId)],
    ty: Type<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    // Determine the field names and types for the struct to be assembled.
    let def_id = ty.get_struct_def().unwrap();
    let def = match builder.cx.struct_def(def_id) {
        Ok(d) => d,
        Err(()) => return builder.error(),
    };
    let fields: Vec<_> = match def
        .fields
        .iter()
        .map(|f| Ok((f.name, builder.cx.map_to_type(f.ty, builder.env)?)))
        .collect::<Result<Vec<_>>>()
    {
        Ok(d) => d,
        Err(()) => return builder.error(),
    };
    let name_lookup: HashMap<Name, usize> = fields
        .iter()
        .enumerate()
        .map(|(i, f)| (f.0.value, i))
        .collect();
    trace!("struct fields are {:?}", fields);
    trace!("struct field names are {:?}", name_lookup);

    // Disassemble the user's mapping into actual field bindings and defaults.
    let mut failed = false;
    let mut default: Option<NodeId> = None;
    let mut type_defaults = HashMap::<Type, &Rvalue>::new();
    let mut values = HashMap::<usize, &Rvalue>::new();
    for &(map, to) in mapping {
        match map {
            PatternMapping::Type(type_id) => match builder.cx.map_to_type(type_id, builder.env) {
                Ok(ty) => {
                    let value = lower_expr_and_cast(builder.cx, to, builder.env, ty);
                    type_defaults.insert(ty, value);
                }
                Err(()) => {
                    failed = true;
                    continue;
                }
            },
            PatternMapping::Member(member_id) => match builder.cx.hir_of(member_id) {
                Ok(HirNode::Expr(&hir::Expr {
                    kind: hir::ExprKind::Ident(name),
                    ..
                })) => {
                    // Determine the index for the mapping.
                    let index = match name_lookup.get(&name.value) {
                        Some(&index) => index,
                        None => {
                            builder.cx.emit(
                                DiagBuilder2::error(format!("`{}` member does not exist", name))
                                    .span(name.span)
                                    .add_note("Struct definition was here:")
                                    .span(builder.cx.span(def_id)),
                            );
                            failed = true;
                            continue;
                        }
                    };

                    // Determine the value and insert into the mappings.
                    let value = lower_expr_and_cast(builder.cx, to, builder.env, fields[index].1);
                    let span = value.span;
                    if let Some(prev) = values.insert(index, value) {
                        builder.cx.emit(
                            DiagBuilder2::warning(format!(
                                "`{}` overwrites previous value `{}` for member `{}`",
                                span.extract(),
                                prev.span.extract(),
                                name
                            ))
                            .span(span)
                            .add_note("Previous value was here:")
                            .span(prev.span),
                        );
                    }
                }
                Ok(_) => {
                    let span = builder.cx.span(member_id);
                    builder.cx.emit(
                        DiagBuilder2::error(format!(
                            "`{}` is not a valid struct member name",
                            span.extract()
                        ))
                        .span(span),
                    );
                    failed = true;
                    continue;
                }
                Err(()) => {
                    failed = true;
                    continue;
                }
            },
            PatternMapping::Default => match default {
                Some(default) => {
                    builder.cx.emit(
                        DiagBuilder2::error("pattern has multiple default mappings")
                            .span(builder.cx.span(to))
                            .add_note("Previous mapping default mapping was here:")
                            .span(builder.cx.span(default)),
                    );
                    failed = true;
                    continue;
                }
                None => {
                    default = Some(to);
                }
            },
        }
    }

    // In case the list of members provided by the user is incomplete, use the
    // defaults to fill in the other members.
    for (index, &(field_name, field_ty)) in fields.iter().enumerate() {
        if values.contains_key(&index) {
            continue;
        }

        // Try the type-based defaults first.
        // TODO(fschuiki): Use better type comparison mechanism that is
        // transparent to user defined types, etc.
        if let Some(default) = type_defaults.get(field_ty) {
            trace!(
                "applying type default to member `{}`: {:?}",
                field_name,
                default
            );
            values.insert(index, default);
            continue;
        }

        // Try to assign a default value.
        let default = if let Some(default) = default {
            default
        } else {
            builder.cx.emit(
                DiagBuilder2::error(format!("`{}` member missing in struct pattern", field_name))
                    .span(builder.span)
                    .add_note("Struct patterns must assign a value to every member."),
            );
            failed = true;
            continue;
        };
        let value = lower_expr_and_cast(builder.cx, default, builder.env, field_ty);
        values.insert(index, value);
    }

    if failed {
        builder.error()
    } else {
        builder.build(
            ty,
            RvalueKind::ConstructStruct((0..values.len()).map(|i| values[&i]).collect()),
        )
    }
}

/// Try to convert a type to its equivalent simple bit vector type.
///
/// All *integral* data types have an equivalent *simple bit vector type*. These
/// include the following:
///
/// - all basic integers
/// - packed arrays
/// - packed structures
/// - packed unions
/// - enums
/// - time (excluded in this implementation)
fn map_to_simple_bit_type<'gcx>(
    cx: &impl Context<'gcx>,
    ty: Type<'gcx>,
    env: ParamEnv,
) -> Option<Type<'gcx>> {
    let bits = match *ty {
        TypeKind::Error | TypeKind::Void | TypeKind::Time => return None,
        TypeKind::Named(_, _, ty) => return map_to_simple_bit_type(cx, ty, env),
        TypeKind::BitVector { .. } => return Some(ty),
        TypeKind::BitScalar { .. } => return Some(ty),
        TypeKind::Bit(..)
        | TypeKind::Int(..)
        | TypeKind::Struct(..)
        | TypeKind::PackedArray(..) => ty::bit_size_of_type(cx, ty, env).ok()?,
    };
    Some(cx.intern_type(TypeKind::BitVector {
        domain: ty::Domain::FourValued, // TODO(fschuiki): check if this is correct
        sign: ty::Sign::Unsigned,
        range: ty::Range {
            size: bits,
            dir: ty::RangeDir::Down,
            offset: 0isize,
        },
        dubbed: false,
    }))
}

/// Same as `map_to_simple_bit_type`, but forces the result to be a vector.
///
/// This operation would commonly be used to cast the operand of an operator
/// which expects a vector. E.g. `foo[4]`.
fn map_to_simple_bit_vector_type<'gcx>(
    cx: &impl Context<'gcx>,
    ty: Type<'gcx>,
    env: ParamEnv,
) -> Option<Type<'gcx>> {
    match map_to_simple_bit_type(cx, ty, env) {
        Some(&TypeKind::BitScalar { domain, sign }) => Some(cx.intern_type(TypeKind::BitVector {
            domain,
            sign,
            range: ty::Range {
                size: 1,
                dir: ty::RangeDir::Down,
                offset: 0isize,
            },
            dubbed: false,
        })),
        x => x,
    }
}

/// Map a unary operator to MIR.
fn lower_unary<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the category of the operation.
    match op {
        hir::UnaryOp::Pos | hir::UnaryOp::Neg => lower_int_unary_arith(builder, ty, op, arg),
        hir::UnaryOp::BitNot => lower_unary_bitwise(builder, ty, op, arg),
        hir::UnaryOp::LogicNot => lower_unary_logic(builder, op, arg),
        hir::UnaryOp::RedAnd
        | hir::UnaryOp::RedOr
        | hir::UnaryOp::RedXor
        | hir::UnaryOp::RedNand
        | hir::UnaryOp::RedNor
        | hir::UnaryOp::RedXnor => lower_reduction(builder, ty, op, arg),
        hir::UnaryOp::PreInc
        | hir::UnaryOp::PreDec
        | hir::UnaryOp::PostInc
        | hir::UnaryOp::PostDec => lower_int_incdec(builder, op, arg),
    }
}

/// Map a binary operator to MIR.
fn lower_binary<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'gcx Rvalue<'gcx> {
    match op {
        hir::BinaryOp::Add
        | hir::BinaryOp::Sub
        | hir::BinaryOp::Mul
        | hir::BinaryOp::Div
        | hir::BinaryOp::Mod
        | hir::BinaryOp::Pow => lower_int_binary_arith(builder, ty, op, lhs, rhs),
        hir::BinaryOp::Eq
        | hir::BinaryOp::Neq
        | hir::BinaryOp::Lt
        | hir::BinaryOp::Leq
        | hir::BinaryOp::Gt
        | hir::BinaryOp::Geq => lower_int_comparison(builder, ty, op, lhs, rhs),
        hir::BinaryOp::LogicShL
        | hir::BinaryOp::LogicShR
        | hir::BinaryOp::ArithShL
        | hir::BinaryOp::ArithShR => lower_shift(builder, ty, op, lhs, rhs),
        hir::BinaryOp::LogicAnd | hir::BinaryOp::LogicOr => {
            lower_binary_logic(builder, op, lhs, rhs)
        }
        hir::BinaryOp::BitAnd
        | hir::BinaryOp::BitOr
        | hir::BinaryOp::BitXor
        | hir::BinaryOp::BitNand
        | hir::BinaryOp::BitNor
        | hir::BinaryOp::BitXnor => lower_binary_bitwise(builder, ty, op, lhs, rhs),
    }
}

/// Map an integer unary arithmetic operator to MIR.
fn lower_int_unary_arith<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the simple bit vector type for the operator.
    let result_ty = match map_to_simple_bit_type(builder.cx, ty, builder.env) {
        Some(ty) => ty,
        None => {
            builder.cx.emit(
                DiagBuilder2::error(format!("`{:?}` cannot operate on `{}`", op, ty))
                    .span(builder.span),
            );
            return builder.error();
        }
    };
    // TODO(fschuiki): Replace this with a query to the operator's internal
    // type.

    // Cast the operands to the operator type.
    trace!("unary {:?} on {} maps to {}", op, ty, result_ty);
    let arg = lower_expr_and_cast(builder.cx, arg, builder.env, result_ty);

    // Determine the operation.
    let op = match op {
        hir::UnaryOp::Pos => return arg,
        hir::UnaryOp::Neg => IntUnaryArithOp::Neg,
        _ => unreachable!("{:?} is not an integer unary arithmetic operator", op),
    };

    // Assemble the node.
    builder.build(
        result_ty,
        RvalueKind::IntUnaryArith {
            op,
            sign: result_ty.get_sign().unwrap(),
            domain: result_ty.get_value_domain().unwrap(),
            arg,
        },
    )
}

/// Map an integer binary arithmetic operator to MIR.
fn lower_int_binary_arith<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the simple bit vector type for the operator.
    let result_ty = match map_to_simple_bit_type(builder.cx, ty, builder.env) {
        Some(ty) => ty,
        None => {
            builder.cx.emit(
                DiagBuilder2::error(format!("`{:?}` cannot operate on `{}`", op, ty))
                    .span(builder.span),
            );
            return builder.error();
        }
    };
    // TODO(fschuiki): Replace this with a query to the operator's internal
    // type.

    // Cast the operands to the operator type.
    trace!("binary {:?} on {} maps to {}", op, ty, result_ty);
    let lhs = lower_expr_and_cast(builder.cx, lhs, builder.env, result_ty);
    let rhs = lower_expr_and_cast(builder.cx, rhs, builder.env, result_ty);

    // Determine the operation.
    let op = match op {
        hir::BinaryOp::Add => IntBinaryArithOp::Add,
        hir::BinaryOp::Sub => IntBinaryArithOp::Sub,
        hir::BinaryOp::Mul => IntBinaryArithOp::Mul,
        hir::BinaryOp::Div => IntBinaryArithOp::Div,
        hir::BinaryOp::Mod => IntBinaryArithOp::Mod,
        hir::BinaryOp::Pow => IntBinaryArithOp::Pow,
        _ => unreachable!("{:?} is not an integer binary arithmetic operator", op),
    };

    // Assemble the node.
    builder.build(
        result_ty,
        RvalueKind::IntBinaryArith {
            op,
            sign: result_ty.get_sign().unwrap(),
            domain: result_ty.get_value_domain().unwrap(),
            lhs,
            rhs,
        },
    )
}

/// Map an integer comparison operator to MIR.
fn lower_int_comparison<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the common type of both operands.
    let (lhs_ty, rhs_ty) = (
        builder.cx.type_of(lhs, builder.env),
        builder.cx.type_of(rhs, builder.env),
    );
    let (lhs_ty, rhs_ty) = match (lhs_ty, rhs_ty) {
        (Ok(l), Ok(r)) => (l, r),
        _ => return builder.error(),
    };
    let (lhs_sbt, rhs_sbt) = (
        map_to_simple_bit_type(builder.cx, lhs_ty, builder.env),
        map_to_simple_bit_type(builder.cx, rhs_ty, builder.env),
    );
    let (lhs_sbt, rhs_sbt) = match (lhs_sbt, rhs_sbt) {
        (Some(l), Some(r)) => (l, r),
        _ => {
            builder.cx.emit(
                DiagBuilder2::error(format!(
                    "`{:?}` cannot operate on `{}` and `{}`",
                    op, lhs_ty, rhs_ty
                ))
                .span(builder.span),
            );
            return builder.error();
        }
    };
    let union_ty = builder.cx.intern_type(TypeKind::BitVector {
        domain: ty::Domain::FourValued,
        sign: ty::Sign::Unsigned,
        range: ty::Range {
            size: max(lhs_sbt.width(), rhs_sbt.width()),
            dir: ty::RangeDir::Down,
            offset: 0isize,
        },
        dubbed: false,
    });
    // TODO(fschuiki): Replace this with a query to the operator's internal
    // type.

    // Cast the operands to the operator type.
    trace!("binary {:?} on {} maps to {}", op, ty, union_ty);
    let lhs = lower_expr_and_cast(builder.cx, lhs, builder.env, union_ty);
    let rhs = lower_expr_and_cast(builder.cx, rhs, builder.env, union_ty);

    // Determine the operation.
    let op = match op {
        hir::BinaryOp::Eq => IntCompOp::Eq,
        hir::BinaryOp::Neq => IntCompOp::Neq,
        hir::BinaryOp::Lt => IntCompOp::Lt,
        hir::BinaryOp::Leq => IntCompOp::Leq,
        hir::BinaryOp::Gt => IntCompOp::Gt,
        hir::BinaryOp::Geq => IntCompOp::Geq,
        _ => unreachable!("{:?} is not an integer binary comparison operator", op),
    };

    // Assemble the node.
    builder.build(
        union_ty.get_value_domain().unwrap().bit_type(),
        RvalueKind::IntComp {
            op,
            sign: union_ty.get_sign().unwrap(),
            domain: union_ty.get_value_domain().unwrap(),
            lhs,
            rhs,
        },
    )
}

/// Map an integer shift operator to MIR.
fn lower_shift<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::BinaryOp,
    value: NodeId,
    amount: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the simple bit vector type for the operator.
    let result_ty = match map_to_simple_bit_type(builder.cx, ty, builder.env) {
        Some(ty) => ty,
        None => {
            builder.cx.emit(
                DiagBuilder2::error(format!("`{}` cannot be shifted", ty)).span(builder.span),
            );
            return builder.error();
        }
    };
    // TODO(fschuiki): Replace this with a query to the operator's internal
    // type.

    // Determine the simple bit vector type for the shift amount.
    let shift_ty = match builder.cx.type_of(amount, builder.env) {
        Ok(t) => t,
        Err(()) => return builder.error(),
    };
    let shift_ty = match map_to_simple_bit_vector_type(builder.cx, shift_ty, builder.env) {
        Some(t) => t,
        None => {
            builder.cx.emit(
                DiagBuilder2::error(format!(
                    "`{}` is not a valid type for a shift amount",
                    shift_ty
                ))
                .span(builder.cx.span(amount)),
            );
            return builder.error();
        }
    };

    // Cast the operands to the operator type.
    trace!("binary {:?} on {} maps to {}", op, ty, result_ty);
    let value = lower_expr_and_cast(builder.cx, value, builder.env, result_ty);
    let amount = lower_expr_and_cast(builder.cx, amount, builder.env, shift_ty);

    // Determine the operation.
    let (op, arith) = match op {
        hir::BinaryOp::LogicShL => (ShiftOp::Left, false),
        hir::BinaryOp::LogicShR => (ShiftOp::Right, false),
        hir::BinaryOp::ArithShL => (ShiftOp::Left, result_ty.is_signed()),
        hir::BinaryOp::ArithShR => (ShiftOp::Right, result_ty.is_signed()),
        _ => unreachable!("{:?} is not an integer shift operator", op),
    };

    // Assemble the node.
    builder.build(
        result_ty,
        RvalueKind::Shift {
            op,
            arith,
            value,
            amount,
        },
    )
}

/// Map a bitwise unary operator to MIR.
fn lower_unary_bitwise<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the simple bit vector type for the operator.
    let result_ty = match map_to_simple_bit_type(builder.cx, ty, builder.env) {
        Some(ty) => ty,
        None => {
            builder.cx.emit(
                DiagBuilder2::error(format!("`{:?}` cannot operate on `{}`", op, ty))
                    .span(builder.span),
            );
            return builder.error();
        }
    };
    // TODO(fschuiki): Replace this with a query to the operator's internal
    // type.

    // Map the argument.
    let arg = lower_expr_and_cast(builder.cx, arg, builder.env, result_ty);

    // Determine the operation.
    let op = match op {
        hir::UnaryOp::BitNot => UnaryBitwiseOp::Not,
        _ => unreachable!("{:?} is not a unary bitwise operator", op),
    };

    // Assemble the node.
    builder.build(result_ty, RvalueKind::UnaryBitwise { op, arg })
}

/// Map a bitwise binary operator to MIR.
fn lower_binary_bitwise<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the simple bit vector type for the operator.
    let result_ty = match map_to_simple_bit_type(builder.cx, ty, builder.env) {
        Some(ty) => ty,
        None => {
            builder.cx.emit(
                DiagBuilder2::error(format!("`{:?}` cannot operate on `{}`", op, ty))
                    .span(builder.span),
            );
            return builder.error();
        }
    };
    // TODO(fschuiki): Replace this with a query to the operator's internal
    // type.

    // Cast the operands to the operator type.
    trace!("binary {:?} on {} maps to {}", op, ty, result_ty);
    let lhs = lower_expr_and_cast(builder.cx, lhs, builder.env, result_ty);
    let rhs = lower_expr_and_cast(builder.cx, rhs, builder.env, result_ty);

    // Determine the operation.
    let (op, negate) = match op {
        hir::BinaryOp::BitAnd => (BinaryBitwiseOp::And, false),
        hir::BinaryOp::BitOr => (BinaryBitwiseOp::Or, false),
        hir::BinaryOp::BitXor => (BinaryBitwiseOp::Xor, false),
        hir::BinaryOp::BitNand => (BinaryBitwiseOp::And, true),
        hir::BinaryOp::BitNor => (BinaryBitwiseOp::Or, true),
        hir::BinaryOp::BitXnor => (BinaryBitwiseOp::Xor, true),
        _ => unreachable!("{:?} is not a binary bitwise operator", op),
    };

    // Assemble the node.
    let value = builder.build(result_ty, RvalueKind::BinaryBitwise { op, lhs, rhs });
    if negate {
        builder.build(
            result_ty,
            RvalueKind::UnaryBitwise {
                op: UnaryBitwiseOp::Not,
                arg: value,
            },
        )
    } else {
        value
    }
}

/// Map a unary logic operator to MIR.
fn lower_unary_logic<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Cast the operand to a boolean.
    let arg = {
        let builder = &builder.with(arg);
        let v = lower_expr(builder.cx, arg, builder.env);
        implicit_cast_to_bool(builder, v)
    };

    // Determine the operation.
    let op = match op {
        hir::UnaryOp::LogicNot => UnaryBitwiseOp::Not,
        _ => unreachable!("{:?} is not a unary logic operator", op),
    };

    // Assemble the node.
    builder.build(&ty::LOGIC_TYPE, RvalueKind::UnaryBitwise { op, arg })
}

/// Map a binary logic operator to MIR.
fn lower_binary_logic<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Cast the operands to a boolean.
    let lhs = {
        let builder = &builder.with(lhs);
        let v = lower_expr(builder.cx, lhs, builder.env);
        implicit_cast_to_bool(builder, v)
    };
    let rhs = {
        let builder = &builder.with(rhs);
        let v = lower_expr(builder.cx, rhs, builder.env);
        implicit_cast_to_bool(builder, v)
    };

    // Determine the operation.
    let op = match op {
        hir::BinaryOp::LogicAnd => BinaryBitwiseOp::And,
        hir::BinaryOp::LogicOr => BinaryBitwiseOp::Or,
        _ => unreachable!("{:?} is not a binary logic operator", op),
    };

    // Assemble the node.
    builder.build(&ty::LOGIC_TYPE, RvalueKind::BinaryBitwise { op, lhs, rhs })
}

/// Map a reduction operator to MIR.
fn lower_reduction<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the simple bit vector type for the operator.
    let inner_ty = match map_to_simple_bit_type(builder.cx, ty, builder.env) {
        Some(ty) => ty,
        None => {
            builder.cx.emit(
                DiagBuilder2::error(format!("`{}` cannot be reduced", ty)).span(builder.span),
            );
            return builder.error();
        }
    };

    // Map the argument.
    let arg = lower_expr_and_cast(builder.cx, arg, builder.env, inner_ty);

    // Determine the operation.
    let (op, negate) = match op {
        hir::UnaryOp::RedAnd => (BinaryBitwiseOp::And, false),
        hir::UnaryOp::RedOr => (BinaryBitwiseOp::Or, false),
        hir::UnaryOp::RedXor => (BinaryBitwiseOp::Xor, false),
        hir::UnaryOp::RedNand => (BinaryBitwiseOp::And, true),
        hir::UnaryOp::RedNor => (BinaryBitwiseOp::Or, true),
        hir::UnaryOp::RedXnor => (BinaryBitwiseOp::Xor, true),
        _ => unreachable!("{:?} is not a reduction operator", op),
    };

    // Assemble the node.
    let bit_ty = inner_ty.get_value_domain().unwrap().bit_type();
    let value = builder.build(bit_ty, RvalueKind::Reduction { op, arg });
    if negate {
        builder.build(
            bit_ty,
            RvalueKind::UnaryBitwise {
                op: UnaryBitwiseOp::Not,
                arg: value,
            },
        )
    } else {
        value
    }
}

/// Generate the nodes necessary to implicitly cast an rvalue to a boolean.
///
/// If the cast is not possible, emit some helpful diagnostics.
fn implicit_cast_to_bool<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    value: &'gcx Rvalue<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    // Map the value to a simple bit type.
    let sbvt = match map_to_simple_bit_type(builder.cx, value.ty, builder.env) {
        Some(sbvt) => sbvt,
        None => {
            builder.cx.emit(
                DiagBuilder2::error(format!(
                    "`{:?}` cannot be cast to a boolean",
                    value.span.extract()
                ))
                .span(value.span),
            );
            return builder.error();
        }
    };

    // Cast to the simple bit type.
    let value = lower_implicit_cast(builder, value, sbvt);

    // If the value already has the equivalent of a one bit value, use that.
    if sbvt.width() == 1 {
        value
    } else {
        builder.build(&ty::BIT_TYPE, RvalueKind::CastToBool(value))
    }
}

/// Map an increment/decrement operator to MIR.
fn lower_int_incdec<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Map the argument to an lvalue and an rvalue.
    let lv = crate::mir::lower::lvalue::lower_expr(builder.cx, arg, builder.env);
    let rv = lower_expr(builder.cx, arg, builder.env);

    // Compute the new value, depending on the operand type.
    let new = if lv.ty.is_bit_scalar() {
        // Single bit values simply toggle the bit.
        builder.build(
            lv.ty,
            RvalueKind::UnaryBitwise {
                op: UnaryBitwiseOp::Not,
                arg: rv,
            },
        )
    } else if lv.ty.is_bit_vector() {
        // Bit vector values add/subtract one.
        let op = match op {
            hir::UnaryOp::PreInc | hir::UnaryOp::PostInc => IntBinaryArithOp::Add,
            hir::UnaryOp::PreDec | hir::UnaryOp::PostDec => IntBinaryArithOp::Sub,
            _ => unreachable!(),
        };
        let one = builder.build(
            lv.ty,
            RvalueKind::Const(builder.cx.intern_value(value::make_int(lv.ty, One::one()))),
        );
        builder.build(
            lv.ty,
            RvalueKind::IntBinaryArith {
                op,
                sign: lv.ty.get_sign().unwrap(),
                domain: lv.ty.get_value_domain().unwrap(),
                lhs: rv,
                rhs: one,
            },
        )
    } else {
        // Everything else we cannot do.
        // TODO(fschuiki): Technically `real` supports this operator as well...
        builder.cx.emit(
            DiagBuilder2::error(format!("`{}` cannot be incremented/decremented", lv.ty))
                .span(builder.span),
        );
        return builder.error();
    };

    // Determine which value to yield as a result.
    let result = match op {
        hir::UnaryOp::PreInc | hir::UnaryOp::PreDec => new,
        hir::UnaryOp::PostInc | hir::UnaryOp::PostDec => rv,
        _ => unreachable!(),
    };

    // Assemble the final assignment node.
    builder.build(
        lv.ty,
        RvalueKind::Assignment {
            lvalue: lv,
            rvalue: new,
            result,
        },
    )
}
