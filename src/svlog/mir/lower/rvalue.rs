// Copyright (c) 2016-2020 Fabian Schuiki

//! Expression rvalue lowering to MIR.

use crate::crate_prelude::*;
use crate::{
    hir::HirNode,
    mir::rvalue::*,
    syntax::ast::BasicNode,
    ty::{SbvType, UnpackedType},
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
    fn build(&self, ty: &'a UnpackedType<'a>, kind: RvalueKind<'a>) -> &'a Rvalue<'a> {
        self.cx.arena().alloc_mir_rvalue(Rvalue {
            id: self.cx.alloc_id(self.span),
            origin: self.expr,
            env: self.env,
            span: self.span,
            ty,
            konst: kind.is_const(),
            kind: kind,
        })
    }

    /// Create an error node.
    ///
    /// This is usually called when something goes wrong during MIR construction
    /// and a marker node is needed to indicate that part of the MIR is invalid.
    fn error(&self) -> &'a Rvalue<'a> {
        self.build(UnpackedType::make_error(), RvalueKind::Error)
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
        Ok(x) => bug_span!(span, cx, "no rvalue for {:?}", x),
        Err(_) => return builder.error(),
    };

    // Determine the cast type.
    let cast = cx.cast_type(expr_id, env).unwrap();

    // Lower the expression.
    let rvalue = lower_expr_inner(&builder, hir, cast.init).unwrap_or_else(|_| builder.error());
    if rvalue.is_error() {
        return rvalue;
    }
    assert_span!(
        rvalue.ty.is_identical(cast.init),
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
    hir: &'gcx hir::Expr<'gcx>,
    ty: &'gcx UnpackedType<'gcx>,
) -> Result<&'gcx Rvalue<'gcx>> {
    let expr_id = hir.id;
    let cx = builder.cx;
    let span = cx.span(expr_id);
    let env = builder.env;
    if ty.is_error() {
        return Err(());
    }

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
        hir::ExprKind::UnsizedConst('x') => Ok(builder.constant(value::make_int(ty, num::one()))),
        hir::ExprKind::UnsizedConst('z') => Ok(builder.constant(value::make_int(ty, num::one()))),
        hir::ExprKind::UnsizedConst(c) => {
            bug_span!(span, cx, "unsized const with weird '{}' char", c)
        }
        hir::ExprKind::TimeConst(ref k) => Ok(builder.constant(value::make_time(k.clone()))),
        hir::ExprKind::StringConst(string) => Ok(builder.constant(value::make_int(
            // TODO: This could use `value::make_string` to build a string
            // value, and then resort to the conversion function there to map
            // the string to the packed vector. Also, escape codes should be
            // handled here.
            ty::PackedType::make_dims(
                cx,
                ty::IntVecType::Bit,
                vec![ty::PackedDim::Range(ty::Range {
                    size: string.value.as_str().len() * 8,
                    dir: ty::RangeDir::Down,
                    offset: 0,
                })],
            )
            .to_unpacked(cx),
            string
                .value
                .as_str()
                .as_bytes()
                .iter()
                .fold(num::zero(), |v, &b| v << 8 | BigInt::from(b)),
        ))),

        // Built-in function calls
        hir::ExprKind::Builtin(hir::BuiltinCall::Unsupported) => {
            Ok(builder.constant(value::make_int(ty, num::zero())))
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(arg)) => {
            let arg_val = cx.constant_value_of(arg, env);
            let arg_int = match arg_val.kind {
                ValueKind::Int(ref arg, ..) => arg,
                ValueKind::Error => return Ok(builder.error()),
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
            let arg_ty = match cx.disamb_type_or_expr(Ref(arg))? {
                &ast::TypeOrExpr::Type(x) => cx.map_to_type_or_error(Ref(x), env),
                &ast::TypeOrExpr::Expr(x) => cx.type_of_expr(Ref(cx.hir_of_expr(Ref(x))?), env),
            };
            match arg_ty.get_bit_size() {
                Some(size) => Ok(builder.constant(value::make_int(ty, size.into()))),
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "value of type `{}` does not have a fixed number of bits",
                            arg_ty
                        ))
                        .span(hir.span()),
                    );
                    Ok(builder.error())
                }
            }
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::CountOnes(_))
        | hir::ExprKind::Builtin(hir::BuiltinCall::OneHot(_))
        | hir::ExprKind::Builtin(hir::BuiltinCall::OneHot0(_)) => {
            bug_span!(span, cx, "unsupported system function {:?}", hir.kind)
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::IsUnknown(_)) => {
            // Since we currently don't emit logic types, this is always zero.
            Ok(builder.constant(value::make_int(ty, num::zero())))
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::ArrayDim(func, arg, dim)) => {
            // Decide which dimension to inspect.
            let dim = match dim {
                Some(dim) => match cx.constant_value_of(dim.id(), env).kind {
                    ValueKind::Int(ref v, ..) => v.to_usize().unwrap(),
                    ValueKind::Error => return Ok(builder.error()),
                    _ => unreachable!(),
                },
                None => 1,
            };

            // Get the fully resolved type of the argument.
            let arg_ty = cx.type_of_expr(Ref(cx.hir_of_expr(Ref(arg))?), env);
            if arg_ty.is_error() {
                return Err(());
            }

            // Extract the dimension of interest.
            let ty_dim = match arg_ty.dims().nth(dim - 1) {
                Some(x) => x,
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "value of type `{}` does not have a dimension {}",
                            arg_ty, dim,
                        ))
                        .span(hir.span())
                        .add_note(format!(
                            "Argument type `{}` has {} dimension(s)",
                            arg_ty.resolve_full(),
                            arg_ty.dims().count()
                        ))
                        .span(arg.span()),
                    );
                    return Err(());
                }
            };

            // Extract the information requested by the array dim function.
            let value = match ty_dim {
                ty::Dim::Packed(ty::PackedDim::Unsized)
                | ty::Dim::Unpacked(ty::UnpackedDim::Unsized)
                | ty::Dim::Unpacked(ty::UnpackedDim::Array(_))
                | ty::Dim::Unpacked(ty::UnpackedDim::Assoc(_))
                | ty::Dim::Unpacked(ty::UnpackedDim::Queue(_)) => 0,
                ty::Dim::Packed(ty::PackedDim::Range(r))
                | ty::Dim::Unpacked(ty::UnpackedDim::Range(r)) => match func {
                    hir::ArrayDim::Left => r.left(),
                    hir::ArrayDim::Right => r.right(),
                    hir::ArrayDim::Low => r.low(),
                    hir::ArrayDim::High => r.high(),
                    hir::ArrayDim::Increment => r.increment(),
                    hir::ArrayDim::Size => r.size as isize,
                },
            };

            Ok(builder.constant(value::make_int(ty, value.into())))
        }

        hir::ExprKind::Ident(..) | hir::ExprKind::Scope(..) => {
            let binding = builder.cx.resolve_node(expr_id, env)?;
            match builder.cx.hir_of(binding)? {
                HirNode::VarDecl(decl) => Ok(builder.build(ty, RvalueKind::Var(decl.id))),
                HirNode::IntPort(port) if ty.resolve_full().core.get_interface().is_some() => {
                    Ok(builder.build(ty, RvalueKind::Intf(port.id)))
                }
                HirNode::IntPort(port) => Ok(builder.build(ty, RvalueKind::Port(port.id))),
                HirNode::Inst(inst) if ty.resolve_full().core.get_interface().is_some() => {
                    Ok(builder.build(ty, RvalueKind::Intf(inst.id)))
                }
                HirNode::EnumVariant(..) | HirNode::ValueParam(..) | HirNode::GenvarDecl(..) => {
                    let k = builder.cx.constant_value_of(binding, env);
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
                    error!("Offending HIR: {:?}", hir);
                    error!("Resolved to: {:?}", x);
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
            assert_type!(true_value.ty, ty, true_value.span, builder.cx);
            assert_type!(false_value.ty, ty, false_value.span, builder.cx);
            Ok(builder.build(
                ty,
                RvalueKind::Ternary {
                    cond,
                    true_value,
                    false_value,
                },
            ))
        }

        hir::ExprKind::PositionalPattern(..)
        | hir::ExprKind::RepeatPattern(..)
        | hir::ExprKind::NamedPattern(..) => Ok(lower_pattern(&builder, hir, ty)),

        hir::ExprKind::Concat(repeat, ref exprs) => {
            // Compute the SBVT for each expression and lower it to MIR,
            // implicitly casting to the SBVT.
            let exprs = exprs
                .iter()
                .map(|&expr| {
                    let value = builder.cx.mir_rvalue(expr, env);
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
                RvalueKind::Concat(exprs.into_iter().map(|(_, v)| v).collect()),
            );

            // If a repetition is present, apply that.
            let repeat = if let Some(repeat) = repeat {
                let count = builder
                    .cx
                    .constant_int_value_of(repeat, env)?
                    .to_usize()
                    .unwrap();
                builder.build(final_ty, RvalueKind::Repeat(count, concat))
            } else {
                concat
            };
            Ok(repeat)
        }

        hir::ExprKind::Index(target, mode) => {
            let (base, length) = compute_indexing(cx, builder.expr, env, mode)?;

            // Cast the target to a simple bit vector type if needed.
            let target = cx.mir_rvalue(target, env);

            // Make sure we can actually index here.
            assert_span!(
                target.ty.dims().next().is_some(),
                target.span,
                cx,
                "cannot index into `{}`; should be handled by typeck",
                target.ty
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

        hir::ExprKind::Field(target, name) => {
            let target_ty = cx.self_determined_type(target, env);
            let value = cx.mir_rvalue(target, env);
            if let Some(intf) = target_ty.and_then(|ty| ty.get_interface()) {
                let def = cx.resolve_hierarchical_or_error(name, intf.ast)?;
                // Distinguish `intf.modport` and `intf.signal`.
                if def.node.as_all().is_modport_name() {
                    Ok(builder.build(ty, value.kind.clone()))
                } else {
                    Ok(builder.build(ty, RvalueKind::IntfSignal(value, def.node.id())))
                }
            } else {
                let (field, _) = cx.resolve_field_access(expr_id, env)?;
                Ok(builder.build(ty, RvalueKind::Member { value, field }))
            }
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
                            out_ty,
                            comp_ty,
                            IntCompOp::Eq,
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
                            out_ty,
                            comp_ty,
                            IntCompOp::Geq,
                            lhs,
                            lo_rv,
                        );
                        let hi_chk = make_int_comparison(
                            &builder.with(hi),
                            out_ty,
                            comp_ty,
                            IntCompOp::Leq,
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

        hir::ExprKind::FunctionCall(..) => {
            bug_span!(
                span,
                cx,
                "lowering of {} to mir not yet supported",
                hir.desc_full()
            );
        }

        hir::ExprKind::Assign { op, lhs, rhs } => Ok(lower_assign(&builder, ty, op, lhs, rhs)),
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
            assert_type!(delta_rvalue.ty, base.ty, delta_rvalue.span, builder.cx);
            let base = builder.build(
                base.ty,
                RvalueKind::IntBinaryArith {
                    op: IntBinaryArithOp::Sub,
                    sign: base.ty.get_simple_bit_vector().unwrap().sign,
                    domain: base.ty.domain(),
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
            let base_ty =
                SbvType::new(ty::Domain::TwoValued, ty::Sign::Signed, max(base.bits(), 1))
                    .to_unpacked(builder.cx);
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
    assert_type!(
        value.ty,
        to.init,
        value.span,
        builder.cx,
        "rvalue type `{}` does not match initial type of cast `{}`",
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
            CastOp::Bool => {
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                value = builder.build(to, RvalueKind::CastToBool(value));
            }
            CastOp::Sign(sign) => {
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                assert_span!(to.is_simple_bit_vector(), value.span, builder.cx);
                value = builder.build(to, RvalueKind::CastSign(sign, value));
            }
            CastOp::Range(range, signed) => {
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                assert_span!(to.is_simple_bit_vector(), value.span, builder.cx);
                let kind = if value.ty.simple_bit_vector(builder.cx, value.span).size < range.size {
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
                        from: value.ty.domain(),
                        to: domain,
                        value,
                    },
                );
            }
            CastOp::PackSBVT => {
                assert_span!(to.is_simple_bit_vector(), value.span, builder.cx);
                value = pack_simple_bit_vector(builder, value);
            }
            CastOp::UnpackSBVT => {
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                value = unpack_simple_bit_vector(builder, value, to);
            }
            CastOp::PickModport => {
                value = builder.build(to, value.kind.clone());
            }
            CastOp::PackString => {
                assert_span!(to.is_simple_bit_vector(), value.span, builder.cx);
                assert_span!(value.ty.is_string(), value.span, builder.cx);
                value = builder.build(to, RvalueKind::PackString(value));
            }
            CastOp::UnpackString => {
                assert_span!(to.is_string(), value.span, builder.cx);
                assert_span!(value.ty.is_simple_bit_vector(), value.span, builder.cx);
                value = builder.build(to, RvalueKind::UnpackString(value));
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
    let to = value
        .ty
        .simple_bit_vector(builder.cx, value.span)
        .forget()
        .to_unpacked(builder.cx);
    if value.ty.coalesces_to_llhd_scalar() {
        builder.build(to, RvalueKind::Transmute(value))
    } else if let Some(dim) = value.ty.outermost_dim() {
        pack_array(builder, value, dim, to)
    } else if let Some(strukt) = value.ty.get_struct() {
        pack_struct(builder, value, strukt, to)
    } else {
        bug_span!(
            value.span,
            builder.cx,
            "cannot pack a `{}` as SBVT",
            value.ty
        );
    }
}

/// Pack a struct as a simple bit vector.
fn pack_struct<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    value: &'a Rvalue<'a>,
    strukt: &'a ty::StructType<'a>,
    to: &'a UnpackedType<'a>,
) -> &'a Rvalue<'a> {
    // Pack each of the fields.
    let mut packed_fields = vec![];
    for (i, field) in strukt.members.iter().enumerate() {
        let field_value = builder.build(field.ty, RvalueKind::Member { value, field: i });
        let field_value = pack_simple_bit_vector(builder, field_value);
        packed_fields.push(field_value);
    }

    // Concatenate the fields.
    builder.build(to, RvalueKind::Concat(packed_fields))
}

/// Pack an array as a simple bit vector.
fn pack_array<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    value: &'a Rvalue<'a>,
    dim: ty::Dim<'a>,
    to: &'a UnpackedType<'a>,
) -> &'a Rvalue<'a> {
    // Determine the length of the array.
    let length = match dim.get_size() {
        Some(x) => x,
        None => bug_span!(
            builder.span,
            builder.cx,
            "pack array with invalid input dimension `{}`",
            dim
        ),
    };

    // Determine the element type.
    let elem_ty = value.ty.pop_dim(builder.cx).unwrap();

    // Catch the trivial case where the core type now is just an integer bit
    // vector type, which is already in the right form.
    if elem_ty.dims().next().is_none() {
        if let Some(ty::PackedCore::IntVec(_)) = elem_ty.get_packed().map(|x| &x.core) {
            return builder.build(to, RvalueKind::Transmute(value));
        }
    }

    // Cast each element.
    let mut packed_elements = vec![];
    let int_ty =
        SbvType::new(ty::Domain::TwoValued, ty::Sign::Unsigned, 32).to_unpacked(builder.cx);
    for i in 0..length {
        let i = builder.build(
            int_ty,
            RvalueKind::Const(builder.cx.intern_value(value::make_int(int_ty, i.into()))),
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
    builder.build(to, RvalueKind::Concat(packed_elements))
}

/// Generate the nodes necessary to unpack a value from its corresponding simple
/// bit vector type.
fn unpack_simple_bit_vector<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    value: &'a Rvalue<'a>,
    to: &'a UnpackedType<'a>,
) -> &'a Rvalue<'a> {
    if value.is_error() {
        return value;
    }
    if to.coalesces_to_llhd_scalar() {
        builder.build(to, RvalueKind::Transmute(value))
    } else if let Some(dim) = to.outermost_dim() {
        unpack_array(builder, value, to, dim)
    } else if let Some(strukt) = to.get_struct() {
        unpack_struct(builder, value, to, strukt)
    } else {
        bug_span!(value.span, builder.cx, "cannot unpack `{}` from SBVT", to);
    }
}

/// Unpack a struct from a simple bit vector.
fn unpack_struct<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    value: &'a Rvalue<'a>,
    to: &'a UnpackedType<'a>,
    strukt: &'a ty::StructType<'a>,
) -> &'a Rvalue<'a> {
    // Unpack each of the fields.
    let mut offset = 0;
    let mut unpacked_fields = vec![];
    for field in &strukt.members {
        let sbvt = field.ty.simple_bit_vector(builder.cx, value.span);
        let ty =
            SbvType::new(ty::Domain::TwoValued, ty::Sign::Unsigned, 32).to_unpacked(builder.cx);
        let w = sbvt.size;
        let i = builder.build(
            ty,
            RvalueKind::Const(builder.cx.intern_value(value::make_int(ty, offset.into()))),
        );
        let value = builder.build(
            sbvt.change_size(w).to_unpacked(builder.cx),
            RvalueKind::Index {
                value,
                base: i,
                length: w,
            },
        );
        let value = unpack_simple_bit_vector(builder, value, field.ty);
        unpacked_fields.push(value);
        offset += w;
    }

    // Construct the struct.
    builder.build(to, RvalueKind::ConstructStruct(unpacked_fields))
}

/// Unpack an array from a simple bit vector.
fn unpack_array<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    value: &'a Rvalue<'a>,
    to: &'a UnpackedType<'a>,
    dim: ty::Dim<'a>,
) -> &'a Rvalue<'a> {
    // Determine the length of the array.
    let length = match dim.get_size() {
        Some(x) => x,
        None => bug_span!(
            builder.span,
            builder.cx,
            "unpack array with invalid input dimension `{}`",
            dim
        ),
    };

    // Determine the element type.
    let elem_ty = to.pop_dim(builder.cx).unwrap();

    // Catch the trivial case where the core type now is just an integer bit
    // vector type, which is already in the right form.
    if elem_ty.dims().next().is_none() {
        if let Some(ty::PackedCore::IntVec(_)) = elem_ty.get_packed().map(|x| &x.core) {
            return builder.build(to, RvalueKind::Transmute(value));
        }
    }

    // Map the element type to its simple bit vector equivalent.
    let sbvt = elem_ty.simple_bit_vector(builder.cx, value.span);
    let w = sbvt.size;

    // Unpack each element.
    let mut unpacked_elements = HashMap::new();
    for i in 0..length {
        let ty =
            SbvType::new(ty::Domain::TwoValued, ty::Sign::Unsigned, 32).to_unpacked(builder.cx);
        let base = builder.build(
            ty,
            RvalueKind::Const(builder.cx.intern_value(value::make_int(ty, (i * w).into()))),
        );
        let elem = builder.build(
            sbvt.to_unpacked(builder.cx),
            RvalueKind::Index {
                value,
                base: base,
                length: w,
            },
        );
        let elem = unpack_simple_bit_vector(builder, elem, elem_ty);
        unpacked_elements.insert(i, elem);
    }

    // Concatenate the elements.
    builder.build(to, RvalueKind::ConstructArray(unpacked_elements))
}

/// Lower a `'{...}` pattern.
fn lower_pattern<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    expr: &'a hir::Expr<'a>,
    ty: &'a UnpackedType<'a>,
) -> &'a Rvalue<'a> {
    // Compute the pattern mapping.
    let map = match builder.cx.map_pattern(Ref(expr), builder.env) {
        Ok(x) => x,
        _ => return builder.error(),
    };
    assert_type!(ty, map.ty, builder.span, builder.cx);

    // Construct the values.
    let values: Vec<_> = map
        .fields
        .iter()
        .map(|&(field, expr)| {
            let value = builder.cx.mir_rvalue(expr.id, builder.env);
            assert_type!(value.ty, field.ty(builder.cx), value.span, builder.cx);
            value
        })
        .collect();

    // Construct the correct output value.
    if ty.coalesces_to_llhd_scalar() {
        if values.len() == 1 {
            values[0]
        } else {
            builder.build(ty, RvalueKind::Concat(values))
        }
    } else if ty.outermost_dim().is_some() {
        builder.build(
            ty,
            // TODO: This should rather be a Vec<>.
            RvalueKind::ConstructArray(values.into_iter().enumerate().collect()),
        )
    } else if ty.get_struct().is_some() {
        builder.build(ty, RvalueKind::ConstructStruct(values))
    } else {
        bug_span!(
            builder.span,
            builder.cx,
            "positional pattern with invalid type `{}`",
            ty
        )
    }
}

/// Map a unary operator to MIR.
fn lower_unary<'gcx>(
    builder: &Builder<'_, impl Context<'gcx>>,
    ty: &'gcx UnpackedType<'gcx>,
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
    ty: &'gcx UnpackedType<'gcx>,
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
        | hir::BinaryOp::Geq => {
            let op_ty = builder.cx.need_operation_type(builder.expr, builder.env);
            if op_ty.is_string() {
                lower_string_comparison(builder, ty, op_ty, op, lhs, rhs)
            } else {
                lower_int_comparison(builder, ty, op_ty, op, lhs, rhs)
            }
        }
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
    result_ty: &'gcx UnpackedType<'gcx>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'gcx Rvalue<'gcx> {
    // Lower the operand.
    let arg = builder.cx.mir_rvalue(arg, builder.env);
    if arg.is_error() {
        return builder.error();
    }

    // Check that the operand is of the right type.
    let sbvt = result_ty.simple_bit_vector(builder.cx, builder.span);
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
            sign: sbvt.sign,
            domain: sbvt.domain,
            arg,
        },
    )
}

/// Map an integer binary arithmetic operator to MIR.
fn lower_int_binary_arith<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'a Rvalue<'a> {
    // Lower the operands.
    let lhs = builder.cx.mir_rvalue(lhs, builder.env);
    let rhs = builder.cx.mir_rvalue(rhs, builder.env);
    if lhs.is_error() || rhs.is_error() {
        return builder.error();
    }

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
    make_int_binary_arith(builder, result_ty, op, lhs, rhs)
}

/// Map an integer binary arithmetic operator to MIR.
pub fn make_int_binary_arith<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: IntBinaryArithOp,
    lhs: &'a Rvalue<'a>,
    rhs: &'a Rvalue<'a>,
) -> &'a Rvalue<'a> {
    // Check that the operands are of the right type.
    let sbvt = result_ty.simple_bit_vector(builder.cx, builder.span);
    assert_type!(lhs.ty, result_ty, builder.span, builder.cx);
    if op != IntBinaryArithOp::Pow {
        assert_type!(rhs.ty, result_ty, builder.span, builder.cx);
    }

    // Assemble the node.
    builder.build(
        result_ty,
        RvalueKind::IntBinaryArith {
            op,
            sign: sbvt.sign,
            domain: sbvt.domain,
            lhs,
            rhs,
        },
    )
}

/// Map an integer comparison operator to MIR.
fn lower_int_comparison<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op_ty: &'a UnpackedType<'a>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'a Rvalue<'a> {
    // Lower the operands.
    let lhs = builder.cx.mir_rvalue(lhs, builder.env);
    let rhs = builder.cx.mir_rvalue(rhs, builder.env);
    if lhs.is_error() || rhs.is_error() || op_ty.is_error() {
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
    make_int_comparison(builder, result_ty, op_ty, op, lhs, rhs)
}

/// Map an integer comparison operator to MIR.
fn make_int_comparison<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op_ty: &'a UnpackedType<'a>,
    op: IntCompOp,
    lhs: &'a Rvalue<'a>,
    rhs: &'a Rvalue<'a>,
) -> &'a Rvalue<'a> {
    // Check that the operands are of the right type.
    let sbvt = op_ty.simple_bit_vector(builder.cx, builder.span);
    assert_type!(lhs.ty, op_ty, builder.span, builder.cx);
    assert_type!(rhs.ty, op_ty, builder.span, builder.cx);

    // Assemble the node.
    builder.build(
        result_ty,
        RvalueKind::IntComp {
            op,
            sign: sbvt.sign,
            domain: sbvt.domain,
            lhs,
            rhs,
        },
    )
}

/// Map a string comparison operator to MIR.
fn lower_string_comparison<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op_ty: &'a UnpackedType<'a>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'a Rvalue<'a> {
    // Lower the operands.
    let lhs = builder.cx.mir_rvalue(lhs, builder.env);
    let rhs = builder.cx.mir_rvalue(rhs, builder.env);
    if lhs.is_error() || rhs.is_error() || op_ty.is_error() {
        return builder.error();
    }

    // Determine the operation.
    let op = match op {
        hir::BinaryOp::Eq => StringCompOp::Eq,
        hir::BinaryOp::Neq => StringCompOp::Neq,
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not a string binary comparison operator",
            op
        ),
    };

    // Check that the operands are of the right type.
    assert_type!(lhs.ty, op_ty, builder.span, builder.cx);
    assert_type!(rhs.ty, op_ty, builder.span, builder.cx);

    // Assemble the node.
    builder.build(result_ty, RvalueKind::StringComp { op, lhs, rhs })
}

/// Map an integer shift operator to MIR.
fn lower_shift<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: hir::BinaryOp,
    value: NodeId,
    amount: NodeId,
) -> &'a Rvalue<'a> {
    // Lower the operands.
    let value = builder.cx.mir_rvalue(value, builder.env);
    let amount = builder.cx.mir_rvalue(amount, builder.env);
    if value.is_error() || amount.is_error() {
        return builder.error();
    }

    // Determine the operation.
    let (op, arith) = match op {
        hir::BinaryOp::LogicShL => (ShiftOp::Left, false),
        hir::BinaryOp::LogicShR => (ShiftOp::Right, false),
        hir::BinaryOp::ArithShL => (ShiftOp::Left, true),
        hir::BinaryOp::ArithShR => (ShiftOp::Right, true),
        _ => bug_span!(
            builder.span,
            builder.cx,
            "{:?} is not an integer shift operator",
            op
        ),
    };

    // Assemble the node.
    make_shift(builder, result_ty, op, arith, value, amount)
}

/// Map an integer shift operator to MIR.
pub fn make_shift<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: ShiftOp,
    arith: bool,
    value: &'a Rvalue<'a>,
    amount: &'a Rvalue<'a>,
) -> &'a Rvalue<'a> {
    // Check that the operands are of the right type.
    let sbvt = result_ty.simple_bit_vector(builder.cx, builder.span);
    assert_type!(value.ty, result_ty, value.span, builder.cx);
    assert_span!(
        amount.ty.get_simple_bit_vector().is_some(),
        amount.span,
        builder.cx
    );

    // Determine the sign of the operation.
    let arith = arith && sbvt.is_signed();

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
fn lower_unary_bitwise<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'a Rvalue<'a> {
    // Lower the operand.
    let arg = builder.cx.mir_rvalue(arg, builder.env);
    if arg.is_error() {
        return builder.error();
    }

    // Check that the operand is of the right type.
    assert_type!(arg.ty, result_ty, arg.span, builder.cx);

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
    builder.build(result_ty, RvalueKind::UnaryBitwise { op, arg })
}

/// Map a bitwise binary operator to MIR.
fn lower_binary_bitwise<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'a Rvalue<'a> {
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
    make_binary_bitwise(builder, result_ty, op, negate, lhs, rhs)
}

/// Map a bitwise binary operator to MIR.
pub fn make_binary_bitwise<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: BinaryBitwiseOp,
    negate: bool,
    lhs: &'a Rvalue<'a>,
    rhs: &'a Rvalue<'a>,
) -> &'a Rvalue<'a> {
    // Check that the operands are of the right type.
    assert_type!(lhs.ty, result_ty, lhs.span, builder.cx);
    assert_type!(rhs.ty, result_ty, rhs.span, builder.cx);

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
fn lower_unary_logic<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'a Rvalue<'a> {
    // Lower the operand.
    let arg = builder.cx.mir_rvalue(arg, builder.env);
    if arg.is_error() {
        return builder.error();
    }

    // Check that the operand is of the right type.
    assert_type!(arg.ty, result_ty, arg.span, builder.cx);

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
    builder.build(result_ty, RvalueKind::UnaryBitwise { op, arg })
}

/// Map a binary logic operator to MIR.
fn lower_binary_logic<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: hir::BinaryOp,
    lhs: NodeId,
    rhs: NodeId,
) -> &'a Rvalue<'a> {
    // Lower the operands.
    let lhs = builder.cx.mir_rvalue(lhs, builder.env);
    let rhs = builder.cx.mir_rvalue(rhs, builder.env);
    if lhs.is_error() || rhs.is_error() {
        return builder.error();
    }

    // Check that the operands are of the right type.
    assert_type!(lhs.ty, result_ty, lhs.span, builder.cx);
    assert_type!(rhs.ty, result_ty, rhs.span, builder.cx);

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
    builder.build(result_ty, RvalueKind::BinaryBitwise { op, lhs, rhs })
}

/// Map a reduction operator to MIR.
fn lower_reduction<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    result_ty: &'a UnpackedType<'a>,
    op: hir::UnaryOp,
    arg: NodeId,
) -> &'a Rvalue<'a> {
    // Determine the operation type.
    let op_ty = builder.cx.need_operation_type(builder.expr, builder.env);

    // Lower the operand.
    let arg = builder.cx.mir_rvalue(arg, builder.env);
    if arg.is_error() || op_ty.is_error() {
        return builder.error();
    }

    // Check the result type.
    assert_span!(
        result_ty.domain() == op_ty.domain(),
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
    let sbvt = lv.ty.simple_bit_vector(builder.cx, builder.span);
    let new = if sbvt.size == 1 {
        // Single bit values simply toggle the bit.
        builder.build(
            lv.ty,
            RvalueKind::UnaryBitwise {
                op: UnaryBitwiseOp::Not,
                arg: rv,
            },
        )
    } else {
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
                sign: sbvt.sign,
                domain: sbvt.domain,
                lhs: rv,
                rhs: one,
            },
        )
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

/// Map an assignment operator to MIR.
fn lower_assign<'a>(
    builder: &Builder<'_, impl Context<'a>>,
    ty: &'a UnpackedType<'a>,
    op: ast::AssignOp,
    lhs: &'a ast::Expr<'a>,
    rhs: &'a ast::Expr<'a>,
) -> &'a Rvalue<'a> {
    // Compute the new value.
    let binop = match op {
        ast::AssignOp::Identity => None,
        ast::AssignOp::Add => Some(hir::BinaryOp::Add),
        ast::AssignOp::Sub => Some(hir::BinaryOp::Sub),
        ast::AssignOp::Mul => Some(hir::BinaryOp::Mul),
        ast::AssignOp::Div => Some(hir::BinaryOp::Div),
        ast::AssignOp::Mod => Some(hir::BinaryOp::Mod),
        ast::AssignOp::BitAnd => Some(hir::BinaryOp::BitAnd),
        ast::AssignOp::BitOr => Some(hir::BinaryOp::BitOr),
        ast::AssignOp::BitXor => Some(hir::BinaryOp::BitXor),
        ast::AssignOp::LogicShL => Some(hir::BinaryOp::LogicShL),
        ast::AssignOp::LogicShR => Some(hir::BinaryOp::LogicShR),
        ast::AssignOp::ArithShL => Some(hir::BinaryOp::ArithShL),
        ast::AssignOp::ArithShR => Some(hir::BinaryOp::ArithShR),
    };
    let rv = if let Some(binop) = binop {
        lower_binary(builder, ty, binop, lhs.id, rhs.id)
    } else {
        builder.cx.mir_rvalue(rhs.id, builder.env)
    };

    // Assemble the final assignment node.
    let lv = builder.cx.mir_lvalue(lhs.id, builder.env);
    builder.build(
        lv.ty,
        RvalueKind::Assignment {
            lvalue: lv,
            rvalue: rv,
            result: rv,
        },
    )
}
