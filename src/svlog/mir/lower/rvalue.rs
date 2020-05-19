// Copyright (c) 2016-2020 Fabian Schuiki

//! Expression rvalue lowering to MIR.

use crate::{
    crate_prelude::*,
    hir::HirNode,
    hir::PatternMapping,
    mir::rvalue::*,
    ty::{Type, TypeKind},
    typeck::{CastOp, CastType},
    value::{self, ValueData, ValueKind},
    ParamEnv,
};
use num::{BigInt, One, Signed, ToPrimitive, Zero};
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

    /// Create a constant node.
    fn constant(&self, value: ValueData<'a>) -> &'a Rvalue<'a> {
        self.build(value.ty, RvalueKind::Const(self.cx.intern_value(value)))
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
    trace!(
        "Lowering `{}` (line {})",
        span.extract(),
        span.begin().human_line()
    );

    // Make sure we have an expression.
    let hir = match cx.hir_of(expr_id) {
        Ok(HirNode::Expr(x)) => x,
        Err(_) => return builder.error(),
        x => bug_span!(span, cx, "no rvalue for {:?}", x),
    };

    // Determine the cast type.
    let cast = cx.cast_type(expr_id, env).unwrap();

    // Lower the expression.
    let rvalue = lower_expr_inner(&builder, hir, cast.init).unwrap_or_else(|_| builder.error());
    assert_span!(
        ty::identical(rvalue.ty, cast.init),
        hir.span,
        cx,
        "rvalue lowering produced type `{}`, expected `{}`",
        rvalue.ty,
        cast.init
    );

    // Lower the casts.
    lower_cast(&builder, rvalue, cast)
}

/// Lower an expression to an rvalue in the MIR.
///
/// May return an error if any of the database queries break.
fn lower_expr_inner<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    hir: &'gcx hir::Expr,
    ty: Type<'gcx>,
) -> Result<&'gcx Rvalue<'gcx>> {
    let expr_id = hir.id;
    let cx = builder.cx;
    let span = cx.span(expr_id);
    let env = builder.env;

    // Determine the expression type and match on the various forms.
    match hir.kind {
        // Literals
        hir::ExprKind::IntConst {
            value: ref k,
            ref special_bits,
            ref x_bits,
            ..
        } => Ok(builder.constant(value::make_int_special(
            ty,
            k.clone(),
            special_bits.clone(),
            x_bits.clone(),
        ))),
        hir::ExprKind::UnsizedConst('0') => Ok(builder.constant(value::make_int(ty, num::zero()))),
        hir::ExprKind::UnsizedConst('1') => Ok(builder.constant(value::make_int(ty, num::one()))),
        hir::ExprKind::TimeConst(ref k) => Ok(builder.constant(value::make_time(k.clone()))),
        hir::ExprKind::StringConst(_) => Ok(builder.constant(value::make_array(
            // TODO(fschuiki): Actually assemble a real string here!
            cx.mkty_packed_array(1, &ty::BYTE_TYPE),
            vec![cx.intern_value(value::make_int(&ty::BYTE_TYPE, num::zero()))],
        ))),

        // Built-in function calls
        hir::ExprKind::Builtin(hir::BuiltinCall::Unsupported) => {
            Ok(builder.constant(value::make_int(ty, num::zero())))
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(arg)) => {
            let arg_val = cx.constant_value_of(arg, env)?;
            let arg_int = match arg_val.kind {
                ValueKind::Int(ref arg, ..) => arg,
                _ => unreachable!(),
            };
            let value = if arg_int <= &BigInt::one() {
                BigInt::zero()
            } else {
                BigInt::from((arg_int - BigInt::one()).bits())
            };
            Ok(builder.constant(value::make_int(ty, value)))
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::Bits(arg)) => {
            let ty = cx.type_of(arg, env)?;
            Ok(builder.constant(value::make_int(
                cx.mkty_int(32),
                ty::bit_size_of_type(cx, ty, env)?.into(),
            )))
        }

        hir::ExprKind::Ident(..) | hir::ExprKind::Scope(..) => {
            let binding = builder.cx.resolve_node(expr_id, env)?;
            match builder.cx.hir_of(binding)? {
                HirNode::VarDecl(decl) => Ok(builder.build(ty, RvalueKind::Var(decl.id))),
                HirNode::IntPort(port) => Ok(builder.build(ty, RvalueKind::Port(port.id))),
                HirNode::EnumVariant(..) | HirNode::ValueParam(..) | HirNode::GenvarDecl(..) => {
                    let k = builder.cx.constant_value_of(binding, env)?;
                    Ok(builder.build(ty, RvalueKind::Const(k)))
                }
                x => {
                    builder.cx.emit(
                        DiagBuilder2::error(format!(
                            "{} cannot be used in an expression",
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
            let cond = cx.mir_rvalue(cond, env);
            let true_value = cx.mir_rvalue(true_value, env);
            let false_value = cx.mir_rvalue(false_value, env);
            assert_span!(
                ty::identical(true_value.ty, ty),
                true_value.span,
                builder.cx
            );
            assert_span!(
                ty::identical(false_value.ty, ty),
                false_value.span,
                builder.cx
            );
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
                    let value = builder.cx.mir_rvalue(expr, env);
                    assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                    Ok((value.ty.try_bit_size(builder.cx, env)?, value))
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

        hir::ExprKind::Index(target, mode) => {
            let (base, length) = compute_indexing(cx, builder.expr, env, mode)?;

            // Cast the target to a simple bit vector type if needed.
            let target_ty = cx.type_of(target, env)?;
            if target_ty.is_error() {
                return Ok(builder.error());
            }
            let target = cx.mir_rvalue(target, env);

            // Make sure we can actually index here.
            assert_span!(
                target.ty.is_array() || target.ty.is_simple_bit_vector(),
                target.span,
                cx,
            );

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
            let value = cx.mir_rvalue(target, env);
            let (_, field, _) = cx.resolve_field_access(expr_id, env)?;
            Ok(builder.build(ty, RvalueKind::Member { value, field }))
        }

        // Casts are handled by the `cast_type` query, and the cast handling
        // that happens after the lowering to an MIR rvalue.
        hir::ExprKind::Cast(_, expr)
        | hir::ExprKind::CastSign(_, expr)
        | hir::ExprKind::CastSize(_, expr)
        | hir::ExprKind::Builtin(hir::BuiltinCall::Signed(expr))
        | hir::ExprKind::Builtin(hir::BuiltinCall::Unsigned(expr)) => Ok(cx.mir_rvalue(expr, env)),

        hir::ExprKind::Inside(expr, ref ranges) => {
            // By default nothing matches.
            let mut check = builder.build(
                ty,
                RvalueKind::Const(cx.intern_value(value::make_int(ty, Zero::zero()))),
            );

            // Determine the intermediate type for the comparisons.
            let comp_ty = cx.need_operation_type(expr_id, env);

            // Determine the result type for the comparison.
            let out_ty = cx.cast_type(expr_id, env).unwrap().init;

            // Compare the LHS against all ranges.
            let lhs = cx.mir_rvalue(expr, env);
            for r in ranges {
                let arg = match r.value {
                    hir::InsideRange::Single(expr) => {
                        // Check if the value matches the LHS.
                        let expr_rv = cx.mir_rvalue(expr, env);
                        make_int_comparison(
                            &builder.with(expr),
                            IntCompOp::Eq,
                            out_ty,
                            comp_ty,
                            lhs,
                            expr_rv,
                        )
                    }
                    hir::InsideRange::Range(lo, hi) => {
                        // Check if the LHS is within [lo:hi], inclusive.
                        let lo_rv = cx.mir_rvalue(lo, env);
                        let hi_rv = cx.mir_rvalue(hi, env);
                        let lo_chk = make_int_comparison(
                            &builder.with(lo),
                            IntCompOp::Geq,
                            out_ty,
                            comp_ty,
                            lhs,
                            lo_rv,
                        );
                        let hi_chk = make_int_comparison(
                            &builder.with(hi),
                            IntCompOp::Leq,
                            out_ty,
                            comp_ty,
                            lhs,
                            hi_rv,
                        );
                        make_binary_bitwise(
                            builder,
                            ty,
                            BinaryBitwiseOp::And,
                            false,
                            lo_chk,
                            hi_chk,
                        )
                    }
                };
                check = make_binary_bitwise(builder, ty, BinaryBitwiseOp::Or, false, check, arg);
            }

            Ok(check)
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
        hir::IndexMode::One(index) => (cx.mir_rvalue(index, env), 0),
        hir::IndexMode::Many(ast::RangeMode::RelativeUp, base, delta) => (
            cx.mir_rvalue(base, env),
            builder
                .cx
                .constant_int_value_of(delta, env)?
                .to_usize()
                .unwrap(),
        ),
        hir::IndexMode::Many(ast::RangeMode::RelativeDown, base, delta) => {
            let base = cx.mir_rvalue(base, env);
            let delta_rvalue = cx.mir_rvalue(delta, env);
            assert_span!(
                ty::identical(delta_rvalue.ty, base.ty),
                delta_rvalue.span,
                builder.cx
            );
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

/// Generate the nodes necessary for a cast operation.
fn lower_cast<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    mut value: &'gcx Rvalue<'gcx>,
    to: CastType<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    // Don't bother with errors.
    if value.is_error() {
        return value;
    }
    if to.is_error() {
        return builder.error();
    }
    assert_span!(
        ty::identical(value.ty, to.init),
        value.span,
        builder.cx,
        "rvalue type `{}` does not match initial type of cast `{}`",
        value.ty,
        to
    );
    trace!(
        "Lowering cast `{}` of `{}` (line {})",
        to,
        value.span.extract(),
        value.span.begin().human_line()
    );

    // Lower each cast individually.
    for &(op, to) in &to.casts {
        debug!("- {:?} from `{}` to `{}`", op, value.ty, to);
        match op {
            CastOp::Bool => {
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                value = builder.build(to, RvalueKind::CastToBool(value));
            }
            CastOp::SimpleBitVector => {
                if value.ty.is_struct() {
                    value = pack_struct(builder, value);
                } else if value.ty.is_array() {
                    value = pack_array(builder, value);
                } else {
                    error!("Cannot map `{}` to a simple bit vector", value.ty);
                }
            }
            CastOp::Sign(sign) => {
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                assert_span!(to.is_simple_bit_vector(), value.span, builder.cx);
                value = builder.build(to, RvalueKind::CastSign(sign, value));
            }
            CastOp::Range(range, signed) => {
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                assert_span!(to.is_simple_bit_vector(), value.span, builder.cx);
                let kind = if value.ty.get_range().unwrap().size < range.size {
                    match signed {
                        true => RvalueKind::SignExtend(range.size, value),
                        false => RvalueKind::ZeroExtend(range.size, value),
                    }
                } else {
                    RvalueKind::Truncate(range.size, value)
                };
                value = builder.build(to, kind);
            }
            CastOp::Domain(domain) => {
                value = builder.build(
                    to,
                    RvalueKind::CastValueDomain {
                        from: value.ty.get_value_domain().unwrap(),
                        to: domain,
                        value,
                    },
                );
            }
            CastOp::Struct => {
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                assert_span!(to.is_struct(), value.span, builder.cx);
                value = unpack_struct(builder, to, value);
            }
            CastOp::Array => {
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                assert_span!(to.is_array(), value.span, builder.cx);
                value = unpack_array(builder, to, value);
            }
            CastOp::Transmute => {
                if let TypeKind::BitScalar { .. } = to {
                    value = builder.build(
                        to,
                        RvalueKind::CastVectorToAtom {
                            domain: value.ty.get_value_domain().unwrap(),
                            value,
                        },
                    );
                } else {
                    value = builder.build(
                        to,
                        RvalueKind::CastAtomToVector {
                            domain: value.ty.get_value_domain().unwrap(),
                            value,
                        },
                    );
                }
            }
        }
        if !ty::identical(value.ty, to) {
            error!(
                "Cast {:?} should have produced `{}`, but value is `{}`",
                op, to, value.ty
            );
        }
    }

    // Check that the casts have actually produced the expected output type.
    assert_span!(
        ty::identical(value.ty, to.ty),
        value.span,
        builder.cx,
        "rvalue type `{}` does not match final cast type `{}` after lower_cast",
        value.ty,
        to.ty
    );
    value
}

/// Generate the nodes necessary to pack a value to its corresponding simple bit
/// vector type.
fn pack_simple_bit_vector<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    value: &'gcx Rvalue<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    if value.is_error() {
        return value;
    }
    let out = if value.ty.is_struct() {
        pack_struct(builder, value)
    } else if value.ty.is_array() {
        pack_array(builder, value)
    } else {
        value
    };
    assert!(out.ty.is_simple_bit_vector());
    out
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
        let field_value = builder.build(field_ty, RvalueKind::Member { value, field: i });
        let field_value = pack_simple_bit_vector(builder, field_value);
        packed_fields.push(field_value);
    }

    // Concatenate the fields.
    if failed {
        builder.error()
    } else {
        let ty = value
            .ty
            .get_simple_bit_vector(builder.cx, builder.env, true)
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
        let elem = pack_simple_bit_vector(builder, elem);
        packed_elements.push(elem);
    }

    // Concatenate the elements.
    let ty = value
        .ty
        .get_simple_bit_vector(builder.cx, builder.env, true)
        .expect("array must have sbvt");
    builder.build(ty, RvalueKind::Concat(packed_elements))
}

/// Unpack a struct from a simple bit vector.
fn unpack_struct<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    value: &'gcx Rvalue<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    let mut failed = false;

    // Get the field names and types.
    let def_id = ty.get_struct_def().unwrap();
    let def = match builder.cx.struct_def(def_id) {
        Ok(d) => d,
        Err(()) => return builder.error(),
    };

    // Unpack each of the fields.
    let mut offset = 0;
    let mut unpacked_fields = vec![];
    for field in &def.fields {
        let field_ty = match builder.cx.map_to_type(field.ty, builder.env) {
            Ok(t) => t,
            Err(()) => {
                failed = true;
                continue;
            }
        };
        let sbvt = field_ty.get_simple_bit_vector(builder.cx, builder.env, true);
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
        let w = sbvt.width();
        let i = builder.build(
            &ty::INT_TYPE,
            RvalueKind::Const(
                builder
                    .cx
                    .intern_value(value::make_int(&ty::INT_TYPE, offset.into())),
            ),
        );
        let field_value = builder.build(
            sbvt,
            RvalueKind::Index {
                value,
                base: i,
                length: w,
            },
        );
        let field_value = pack_simple_bit_vector(builder, field_value);
        unpacked_fields.push(field_value);
        offset += w;
    }

    // Construct the struct.
    if failed {
        builder.error()
    } else {
        builder.build(ty, RvalueKind::ConstructStruct(unpacked_fields))
    }
}

/// Unpack an array from a simple bit vector.
fn unpack_array<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    value: &'gcx Rvalue<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    // Unpack the outermost array dimension.
    let length = ty.get_array_length().expect("array length");

    // Map the element type to its simple bit vector equivalent.
    let elem_ty = ty.get_array_element().expect("array element type");
    let sbvt = match elem_ty.get_simple_bit_vector(builder.cx, builder.env, true) {
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
    let w = sbvt.width();

    // Unpack each element.
    let mut unpacked_elements = HashMap::new();
    for i in 0..length {
        let base = builder.build(
            &ty::INT_TYPE,
            RvalueKind::Const(
                builder
                    .cx
                    .intern_value(value::make_int(&ty::INT_TYPE, (i * w).into())),
            ),
        );
        let elem = builder.build(
            sbvt,
            RvalueKind::Index {
                value,
                base: base,
                length: w,
            },
        );
        let elem = pack_simple_bit_vector(builder, elem);
        unpacked_elements.insert(i, elem);
    }

    // Concatenate the elements.
    builder.build(ty, RvalueKind::ConstructArray(unpacked_elements))
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
                        ValueKind::Int(i, ..) => i - num::BigInt::from(offset),
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
                let value = builder.cx.mir_rvalue(to, builder.env);
                assert_type!(value.ty, elem_ty, value.span, builder.cx);
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
                    let value = builder.cx.mir_rvalue(to, builder.env);
                    assert_type!(value.ty, elem_ty, value.span, builder.cx);
                    default = Some(value);
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
                    let value = builder.cx.mir_rvalue(to, builder.env);
                    assert_type!(value.ty, ty, value.span, builder.cx);
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
                    let value = builder.cx.mir_rvalue(to, builder.env);
                    assert_span!(
                        ty::identical(value.ty, fields[index].1),
                        value.span,
                        builder.cx
                    );
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
        let value = builder.cx.mir_rvalue(default, builder.env);
        assert_type!(value.ty, field_ty, value.span, builder.cx);
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
        hir::UnaryOp::LogicNot => lower_unary_logic(builder, ty, op, arg),
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
            lower_binary_logic(builder, ty, op, lhs, rhs)
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
    result_ty: Type<'gcx>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Lower the operand.
    let arg = builder.cx.mir_rvalue(arg, builder.env);
    if arg.is_error() {
        return builder.error();
    }

    // Check that the operand is of the right type.
    assert_type!(arg.ty, result_ty, builder.span, builder.cx);

    // Determine the operation.
    let op = match op {
        hir::UnaryOp::Pos => return arg,
        hir::UnaryOp::Neg => IntUnaryArithOp::Neg,
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not an integer unary arithmetic operator",
            op
        ),
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
    result_ty: Type<'gcx>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Lower the operands.
    let lhs = builder.cx.mir_rvalue(lhs, builder.env);
    let rhs = builder.cx.mir_rvalue(rhs, builder.env);
    if lhs.is_error() || rhs.is_error() {
        return builder.error();
    }

    // Check that the operands are of the right type.
    assert_type!(lhs.ty, result_ty, builder.span, builder.cx);
    assert_type!(rhs.ty, result_ty, builder.span, builder.cx);

    // Determine the operation.
    let op = match op {
        hir::BinaryOp::Add => IntBinaryArithOp::Add,
        hir::BinaryOp::Sub => IntBinaryArithOp::Sub,
        hir::BinaryOp::Mul => IntBinaryArithOp::Mul,
        hir::BinaryOp::Div => IntBinaryArithOp::Div,
        hir::BinaryOp::Mod => IntBinaryArithOp::Mod,
        hir::BinaryOp::Pow => IntBinaryArithOp::Pow,
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not an integer binary arithmetic operator",
            op
        ),
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
    result_ty: Type<'gcx>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the operation type of the comparison.
    let ty = builder.cx.need_operation_type(builder.expr, builder.env);

    // Lower the operands.
    let lhs = builder.cx.mir_rvalue(lhs, builder.env);
    let rhs = builder.cx.mir_rvalue(rhs, builder.env);
    if lhs.is_error() || rhs.is_error() || ty.is_error() {
        return builder.error();
    }

    // Determine the operation.
    let op = match op {
        hir::BinaryOp::Eq => IntCompOp::Eq,
        hir::BinaryOp::Neq => IntCompOp::Neq,
        hir::BinaryOp::Lt => IntCompOp::Lt,
        hir::BinaryOp::Leq => IntCompOp::Leq,
        hir::BinaryOp::Gt => IntCompOp::Gt,
        hir::BinaryOp::Geq => IntCompOp::Geq,
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not an integer binary comparison operator",
            op
        ),
    };

    // Assemble the node.
    make_int_comparison(builder, op, result_ty, ty, lhs, rhs)
}

/// Map an integer comparison operator to MIR.
fn make_int_comparison<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    op: IntCompOp,
    result_ty: Type<'gcx>,
    op_ty: Type<'gcx>,
    lhs: &'gcx Rvalue<'gcx>,
    rhs: &'gcx Rvalue<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    // Check that the operands are of the right type.
    assert_type!(lhs.ty, op_ty, builder.span, builder.cx);
    assert_type!(rhs.ty, op_ty, builder.span, builder.cx);

    // Assemble the node.
    builder.build(
        result_ty,
        RvalueKind::IntComp {
            op,
            sign: op_ty.get_sign().unwrap(),
            domain: op_ty.get_value_domain().unwrap(),
            lhs,
            rhs,
        },
    )
}

/// Map an integer shift operator to MIR.
fn lower_shift<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    result_ty: Type<'gcx>,
    op: hir::BinaryOp,
    value: NodeId,
    amount: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Lower the operands.
    let value = builder.cx.mir_rvalue(value, builder.env);
    let amount = builder.cx.mir_rvalue(amount, builder.env);
    if value.is_error() || amount.is_error() {
        return builder.error();
    }

    // Check that the operands are of the right type.
    assert_type!(value.ty, result_ty, value.span, builder.cx);
    assert_span!(amount.ty.is_simple_bit_vector(), amount.span, builder.cx);

    // Determine the operation.
    let (op, arith) = match op {
        hir::BinaryOp::LogicShL => (ShiftOp::Left, false),
        hir::BinaryOp::LogicShR => (ShiftOp::Right, false),
        hir::BinaryOp::ArithShL => (ShiftOp::Left, result_ty.is_signed()),
        hir::BinaryOp::ArithShR => (ShiftOp::Right, result_ty.is_signed()),
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not an integer shift operator",
            op
        ),
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
    // Lower the operand.
    let arg = builder.cx.mir_rvalue(arg, builder.env);
    if arg.is_error() {
        return builder.error();
    }

    // Check that the operand is of the right type.
    assert_type!(arg.ty, ty, arg.span, builder.cx);

    // Determine the operation.
    let op = match op {
        hir::UnaryOp::BitNot => UnaryBitwiseOp::Not,
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not a unary bitwise operator",
            op
        ),
    };

    // Assemble the node.
    builder.build(ty, RvalueKind::UnaryBitwise { op, arg })
}

/// Map a bitwise binary operator to MIR.
fn lower_binary_bitwise<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Lower the operands.
    let lhs = builder.cx.mir_rvalue(lhs, builder.env);
    let rhs = builder.cx.mir_rvalue(rhs, builder.env);
    if lhs.is_error() || rhs.is_error() {
        return builder.error();
    }

    // Determine the operation.
    let (op, negate) = match op {
        hir::BinaryOp::BitAnd => (BinaryBitwiseOp::And, false),
        hir::BinaryOp::BitOr => (BinaryBitwiseOp::Or, false),
        hir::BinaryOp::BitXor => (BinaryBitwiseOp::Xor, false),
        hir::BinaryOp::BitNand => (BinaryBitwiseOp::And, true),
        hir::BinaryOp::BitNor => (BinaryBitwiseOp::Or, true),
        hir::BinaryOp::BitXnor => (BinaryBitwiseOp::Xor, true),
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not a binary bitwise operator",
            op
        ),
    };

    // Assemble the node.
    make_binary_bitwise(builder, ty, op, negate, lhs, rhs)
}

/// Map a bitwise binary operator to MIR.
fn make_binary_bitwise<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: BinaryBitwiseOp,
    negate: bool,
    lhs: &'gcx Rvalue<'gcx>,
    rhs: &'gcx Rvalue<'gcx>,
) -> &'gcx Rvalue<'gcx> {
    // Check that the operands are of the right type.
    assert_type!(lhs.ty, ty, lhs.span, builder.cx);
    assert_type!(rhs.ty, ty, rhs.span, builder.cx);

    // Assemble the node.
    let value = builder.build(ty, RvalueKind::BinaryBitwise { op, lhs, rhs });
    if negate {
        builder.build(
            ty,
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
    ty: Type<'gcx>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Lower the operand.
    let arg = builder.cx.mir_rvalue(arg, builder.env);
    if arg.is_error() {
        return builder.error();
    }

    // Check that the operand is of the right type.
    assert_type!(arg.ty, ty, arg.span, builder.cx);

    // Determine the operation.
    let op = match op {
        hir::UnaryOp::LogicNot => UnaryBitwiseOp::Not,
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not a unary logic operator",
            op
        ),
    };

    // Assemble the node.
    builder.build(ty, RvalueKind::UnaryBitwise { op, arg })
}

/// Map a binary logic operator to MIR.
fn lower_binary_logic<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: Type<'gcx>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Lower the operands.
    let lhs = builder.cx.mir_rvalue(lhs, builder.env);
    let rhs = builder.cx.mir_rvalue(rhs, builder.env);
    if lhs.is_error() || rhs.is_error() {
        return builder.error();
    }

    // Check that the operands are of the right type.
    assert_type!(lhs.ty, ty, lhs.span, builder.cx);
    assert_type!(rhs.ty, ty, rhs.span, builder.cx);

    // Determine the operation.
    let op = match op {
        hir::BinaryOp::LogicAnd => BinaryBitwiseOp::And,
        hir::BinaryOp::LogicOr => BinaryBitwiseOp::Or,
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not a binary logic operator",
            op
        ),
    };

    // Assemble the node.
    builder.build(ty, RvalueKind::BinaryBitwise { op, lhs, rhs })
}

/// Map a reduction operator to MIR.
fn lower_reduction<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    result_ty: Type<'gcx>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Determine the operation type.
    let op_ty = builder.cx.need_operation_type(builder.expr, builder.env);

    // Lower the operand.
    let arg = builder.cx.mir_rvalue(arg, builder.env);
    if arg.is_error() || op_ty.is_error() {
        return builder.error();
    }

    // Check the result type.
    assert_span!(
        ty::identical(result_ty, op_ty.get_value_domain().unwrap().bit_type()),
        builder.span,
        builder.cx
    );

    // Check that the operand is of the right type.
    assert_type!(arg.ty, op_ty, builder.span, builder.cx);

    // Determine the operation.
    let (op, negate) = match op {
        hir::UnaryOp::RedAnd => (BinaryBitwiseOp::And, false),
        hir::UnaryOp::RedOr => (BinaryBitwiseOp::Or, false),
        hir::UnaryOp::RedXor => (BinaryBitwiseOp::Xor, false),
        hir::UnaryOp::RedNand => (BinaryBitwiseOp::And, true),
        hir::UnaryOp::RedNor => (BinaryBitwiseOp::Or, true),
        hir::UnaryOp::RedXnor => (BinaryBitwiseOp::Xor, true),
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not a reduction operator",
            op
        ),
    };

    // Assemble the node.
    let value = builder.build(result_ty, RvalueKind::Reduction { op, arg });
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

/// Map an increment/decrement operator to MIR.
fn lower_int_incdec<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Map the argument to an lvalue and an rvalue.
    let lv = builder.cx.mir_lvalue(arg, builder.env);
    let rv = builder.cx.mir_rvalue(arg, builder.env);
    if lv.is_error() || rv.is_error() {
        return builder.error();
    }

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
            DiagBuilder2::error(format!(
                "value of type `{}` cannot be incremented/decremented",
                lv.ty
            ))
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
