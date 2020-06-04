// Copyright (c) 2016-2020 Fabian Schuiki

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{Domain, PackedType, SbvType, Sign, Type, TypeKind, UnpackedType},
    value::ValueKind,
    ParamEnv, ParamEnvBinding,
};
use num::{cast::ToPrimitive, BigInt, One, Signed};

/// Determine the type of a node.
#[moore_derive::query]
pub(crate) fn type_of<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Type<'a>> {
    let hir = cx.hir_of(node_id)?;
    #[allow(unreachable_patterns)]
    match hir {
        HirNode::IntPort(p) => match &p.data {
            Some(data) => cx.map_to_type(data.ty, env),
            None => {
                // Resolve the port to a net/var decl in the module, then use
                // that decl's type.
                let decl_id = cx.resolve_node(node_id, env)?;
                cx.type_of(decl_id, env)
            }
        },
        HirNode::ExtPort(p) => {
            if p.exprs.len() == 1 {
                let expr = &p.exprs[0];
                if !expr.selects.is_empty() {
                    bug_span!(
                        p.span,
                        cx,
                        "port{} contains a `[...]` selection; not yet supported in typeck",
                        p.name
                            .map(|n| format!(" `{}`", n))
                            .unwrap_or_else(String::new)
                    );
                }
                let module = match cx.hir_of(p.module)? {
                    HirNode::Module(m) => m,
                    _ => unreachable!(),
                };
                cx.type_of(module.ports_new.int[expr.port].id, env)
            } else {
                bug_span!(
                    p.span,
                    cx,
                    "port{} is a concatenation; not yet supported in typeck",
                    p.name
                        .map(|n| format!(" `{}`", n))
                        .unwrap_or_else(String::new)
                );
            }
        }
        HirNode::Expr(_) => Ok(cx.cast_type(node_id, env).unwrap().ty.to_legacy(cx)),
        HirNode::ValueParam(p) => {
            if is_explicit_type(cx, p.ty)? {
                return cx.map_to_type(p.ty, env);
            }
            let env_data = cx.param_env_data(env);
            match env_data.find_value(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.type_of(assigned_id.id(), assigned_id.env())
                }
                Some(ParamEnvBinding::Direct(t)) => return Ok(t.ty.to_legacy(cx)),
                _ => (),
            }
            if let Some(default) = p.default {
                return cx.type_of(default, env);
            }
            cx.emit(
                DiagBuilder2::error(format!(
                    "{} has implicit type but was not assigned and has no default",
                    p.desc_full()
                ))
                .span(p.human_span())
                .add_note("specify a type for the parameter; or")
                .add_note("add a default value for the parameter; or")
                .add_note("override the parameter from outside"),
            );
            Err(())
        }
        HirNode::VarDecl(d) => {
            if is_explicit_type(cx, d.ty)? {
                cx.map_to_type(d.ty, env)
            } else if let Some(init) = d.init {
                cx.type_of(init, env)
            } else if let hir::VarKind::Net { .. } = d.kind {
                Ok(&ty::LOGIC_TYPE)
            } else {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "{} has implicit type but is not initialized",
                        d.desc_full()
                    ))
                    .span(d.human_span())
                    .add_note("specify a type for the variable; or")
                    .add_note("add an initial value"),
                );
                Err(())
            }
        }
        HirNode::GenvarDecl(_) => Ok(&ty::INT_TYPE),
        HirNode::EnumVariant(v) => {
            // TODO: This is ultra hacky. The enum itself does not get its own
            // node ID, but rather shares this with the associated array dims.
            // So we nee to unpack those here again. This is horribly ugly and
            // should rather be done differently. E.g. by having the AST be more
            // of an ID-based graph.
            let hir = match cx.hir_of(v.enum_id)? {
                HirNode::Type(hir) => hir,
                _ => unreachable!(),
            };
            let mut kind = &hir.kind;
            loop {
                kind = match kind {
                    hir::TypeKind::PackedArray(ref inner, ..) => inner.as_ref(),
                    _ => break,
                }
            }
            map_type_kind(cx, v.enum_id, env, hir, kind)
        }
        HirNode::Package(_) => Ok(&ty::VOID_TYPE),
        HirNode::Assign(_) => unreachable!("has no type: {:?}", hir),
        _ => {
            error!("{:#?}", hir);
            panic!(
                "{}",
                DiagBuilder2::bug(format!(
                    "type analysis of {} not implemented",
                    hir.desc_full()
                ))
                .span(hir.span())
            )
        }
    }
}

/// Determine the type of an expression.
#[moore_derive::query]
pub(crate) fn type_of_expr<'a>(
    cx: &impl Context<'a>,
    expr: Ref<'a, hir::Expr>,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    let Ref(expr) = expr;
    match expr.kind {
        // These expressions are have a fully self-determined type.
        hir::ExprKind::IntConst { .. }
        | hir::ExprKind::TimeConst(..)
        | hir::ExprKind::StringConst(..)
        | hir::ExprKind::Ident(..)
        | hir::ExprKind::Scope(..)
        | hir::ExprKind::Concat(..)
        | hir::ExprKind::Cast(..)
        | hir::ExprKind::CastSign(..)
        | hir::ExprKind::CastSize(..)
        | hir::ExprKind::Inside(..)
        | hir::ExprKind::Builtin(hir::BuiltinCall::Unsupported)
        | hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(_))
        | hir::ExprKind::Builtin(hir::BuiltinCall::Bits(_))
        | hir::ExprKind::Field(..)
        | hir::ExprKind::Index(..) => cx.need_self_determined_type(expr.id, env),

        // Unsized constants infer their type from the context if possible, and
        // otherwise fall back to a self-determined mode.
        hir::ExprKind::UnsizedConst(..) => cx
            .type_context(expr.id, env)
            .and_then(|x| x.ty().get_simple_bit_vector())
            .map(|x| x.to_unpacked(cx))
            .unwrap_or_else(|| cx.need_self_determined_type(expr.id, env)),

        // Unary operators either return their internal operation type, or they
        // evaluate to a fully self-determined type.
        hir::ExprKind::Unary(op, _) => {
            match op {
                // Most operators simply evaluate to their operation type.
                hir::UnaryOp::Neg
                | hir::UnaryOp::Pos
                | hir::UnaryOp::BitNot
                | hir::UnaryOp::PreInc
                | hir::UnaryOp::PreDec
                | hir::UnaryOp::PostInc
                | hir::UnaryOp::PostDec => cx.need_operation_type(expr.id, env),

                // And some have a fixed return type.
                hir::UnaryOp::LogicNot
                | hir::UnaryOp::RedAnd
                | hir::UnaryOp::RedOr
                | hir::UnaryOp::RedXor
                | hir::UnaryOp::RedNand
                | hir::UnaryOp::RedNor
                | hir::UnaryOp::RedXnor => cx.need_self_determined_type(expr.id, env),
            }
        }

        // Binary operators either return their internal operation type, or they
        // evaluate to a fully self-determined type.
        hir::ExprKind::Binary(op, _, _) => {
            match op {
                // Most operators simply evaluate to their operation type.
                hir::BinaryOp::Add
                | hir::BinaryOp::Sub
                | hir::BinaryOp::Mul
                | hir::BinaryOp::Div
                | hir::BinaryOp::Mod
                | hir::BinaryOp::Pow
                | hir::BinaryOp::LogicShL
                | hir::BinaryOp::LogicShR
                | hir::BinaryOp::ArithShL
                | hir::BinaryOp::ArithShR
                | hir::BinaryOp::BitAnd
                | hir::BinaryOp::BitNand
                | hir::BinaryOp::BitOr
                | hir::BinaryOp::BitNor
                | hir::BinaryOp::BitXor
                | hir::BinaryOp::BitXnor => cx.need_operation_type(expr.id, env),

                // And some have a fixed return type.
                hir::BinaryOp::Eq
                | hir::BinaryOp::Neq
                | hir::BinaryOp::Lt
                | hir::BinaryOp::Leq
                | hir::BinaryOp::Gt
                | hir::BinaryOp::Geq
                | hir::BinaryOp::LogicAnd
                | hir::BinaryOp::LogicOr => cx.need_self_determined_type(expr.id, env),
            }
        }

        // Ternary operators return their internal operation type.
        hir::ExprKind::Ternary(..) => cx.need_operation_type(expr.id, env),

        // Other things simply evaluate to their self-determined type.
        hir::ExprKind::Builtin(hir::BuiltinCall::Signed(_))
        | hir::ExprKind::Builtin(hir::BuiltinCall::Unsigned(_))
        | hir::ExprKind::FunctionCall(..) => cx.need_self_determined_type(expr.id, env),

        // Pattern expressions require a type context.
        hir::ExprKind::PositionalPattern(..)
        | hir::ExprKind::NamedPattern(..)
        | hir::ExprKind::RepeatPattern(..) => cx.need_type_context(expr.id, env).ty(),
    }
}

/// Convert a node to a type.
#[moore_derive::query]
pub(crate) fn map_to_type<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Type<'a>> {
    let hir = cx.hir_of(node_id)?;
    #[allow(unreachable_patterns)]
    match hir {
        HirNode::Type(hir) => map_type_kind(cx, node_id, env, hir, &hir.kind),
        HirNode::TypeParam(param) => {
            let env_data = cx.param_env_data(env);
            match env_data.find_type(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.map_to_type(assigned_id.id(), assigned_id.env())
                }
                Some(ParamEnvBinding::Direct(t)) => return Ok(t),
                _ => (),
            }
            if let Some(default) = param.default {
                return cx.map_to_type(default, env);
            }
            let d = DiagBuilder2::error(format!(
                "{} not assigned and has no default",
                param.desc_full(),
            ));
            let contexts = cx.param_env_contexts(env);
            for &context in &contexts {
                cx.emit(
                    d.clone()
                        .span(cx.span(context))
                        .add_note("parameter declared here:")
                        .span(param.human_span()),
                );
            }
            if contexts.is_empty() {
                cx.emit(d.span(param.human_span()));
            }
            Err(())
        }
        HirNode::Typedef(def) => cx.map_to_type(def.ty, env),

        // Certain expressions are actually types. In that case we also support
        // a mapping to a type.
        HirNode::Expr(hir) => match hir.kind {
            hir::ExprKind::Ident(name) => {
                let binding = cx.resolve_upwards_or_error(name, node_id)?;
                Ok(cx.mkty_named(name, binding.env(env)))
            }
            hir::ExprKind::Scope(scope_id, name) => {
                let within = cx.resolve_node(scope_id, env)?;
                let binding = cx.resolve_downwards_or_error(name, within)?;
                Ok(cx.mkty_named(name, binding.env(env)))
            }
            _ => {
                error!("{:#?}", hir);
                cx.emit(
                    DiagBuilder2::error(format!("{} is not a type", hir.desc_full()))
                        .span(hir.span()),
                );
                Err(())
            }
        },
        _ => cx.unimp_msg("conversion to type of", &hir),
    }
}

/// Check if a type (given by its node id) is explicit.
fn is_explicit_type<'gcx>(cx: &impl Context<'gcx>, node_id: NodeId) -> Result<bool> {
    Ok(match cx.hir_of(node_id)? {
        HirNode::Type(x) => x.is_explicit(),
        _ => false,
    })
}

/// Map an HIR type into the type system.
///
/// This essentially converts `hir::TypeKind` to `Type`.
fn map_type_kind<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
    root: &hir::Type,
    kind: &hir::TypeKind,
) -> Result<Type<'gcx>> {
    #[allow(unreachable_patterns)]
    match *kind {
        hir::TypeKind::Builtin(hir::BuiltinType::Void) => Ok(cx.mkty_void()),
        hir::TypeKind::Builtin(hir::BuiltinType::Bit) => Ok(&ty::BIT_TYPE),
        hir::TypeKind::Builtin(hir::BuiltinType::Logic) => Ok(&ty::LOGIC_TYPE),
        hir::TypeKind::Builtin(hir::BuiltinType::Byte) => Ok(&ty::BYTE_TYPE),
        hir::TypeKind::Builtin(hir::BuiltinType::ShortInt) => Ok(&ty::SHORTINT_TYPE),
        hir::TypeKind::Builtin(hir::BuiltinType::Int) => Ok(&ty::INT_TYPE),
        hir::TypeKind::Builtin(hir::BuiltinType::Integer) => Ok(&ty::INTEGER_TYPE),
        hir::TypeKind::Builtin(hir::BuiltinType::LongInt) => Ok(&ty::LONGINT_TYPE),
        hir::TypeKind::Builtin(hir::BuiltinType::Time) => Ok(&ty::TIME_TYPE),
        hir::TypeKind::Builtin(hir::BuiltinType::String) => {
            Ok(cx.mkty_packed_array(1, &ty::BYTE_TYPE))
        }
        hir::TypeKind::Named(name) => {
            let binding = cx.resolve_upwards_or_error(name, node_id)?;
            Ok(cx.mkty_named(name, binding.env(env)))
        }
        hir::TypeKind::Scope(scope_id, name) => {
            let within = cx.resolve_node(scope_id, env)?;
            let binding = cx.resolve_downwards_or_error(name, within)?;
            Ok(cx.mkty_named(name, binding.env(env)))
        }
        hir::TypeKind::Struct(..) => Ok(cx.mkty_struct(node_id.env(env))),
        hir::TypeKind::PackedArray(ref inner, lhs, rhs) => {
            let map_bound = |bound: NodeId| -> Result<&num::BigInt> {
                match cx.constant_value_of(bound, env)?.kind {
                    ValueKind::Int(ref int, ..) => Ok(int),
                    ValueKind::Error => Err(()),
                    _ => {
                        let span = cx.span(bound);
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "array bound `{}` is not an integer",
                                span.extract()
                            ))
                            .span(span),
                        );
                        return Err(());
                    }
                }
            };
            let lhs = map_bound(lhs)?;
            let rhs = map_bound(rhs)?;
            let (dir, lo, hi) = if lhs < rhs {
                (ty::RangeDir::Up, lhs, rhs)
            } else {
                (ty::RangeDir::Down, rhs, lhs)
            };
            let size = (hi - lo) + num::BigInt::one();
            let size = match size.to_usize() {
                Some(i) => i,
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!("{} is too large", kind.desc_full()))
                            .span(root.human_span())
                            .add_note(format!("array would contain {} elements", size)),
                    );
                    return Err(());
                }
            };
            let offset = lo.to_isize().unwrap();
            match **inner {
                hir::TypeKind::Implicit | hir::TypeKind::Builtin(hir::BuiltinType::Bit) => Ok(cx
                    .intern_type(TypeKind::BitVector {
                        domain: ty::Domain::TwoValued,
                        sign: ty::Sign::Unsigned,
                        range: ty::Range { size, dir, offset },
                        dubbed: false,
                    })),
                hir::TypeKind::Builtin(hir::BuiltinType::Logic) => {
                    Ok(cx.intern_type(TypeKind::BitVector {
                        domain: ty::Domain::FourValued,
                        sign: ty::Sign::Unsigned,
                        range: ty::Range { size, dir, offset },
                        dubbed: false,
                    }))
                }
                _ => {
                    let inner_ty = map_type_kind(cx, node_id, env, root, inner)?;
                    Ok(cx.mkty_packed_array(size, inner_ty))
                }
            }
        }
        hir::TypeKind::Enum(ref variants, repr) => match repr {
            Some(repr) => cx.map_to_type(repr, env),
            None => Ok(cx.mkty_int(variants.len().next_power_of_two().trailing_zeros() as usize)),
        },

        hir::TypeKind::RefExpr(expr) => cx.type_of(expr, env),
        hir::TypeKind::RefType(ty) => cx.map_to_type(ty, env),

        // We should never request mapping of an implicit type. Rather, the
        // actual type should be mapped. Arriving here is a bug in the
        // calling function.
        hir::TypeKind::Implicit => {
            error!("{:#?}", root);
            unreachable!(
                "{}",
                DiagBuilder2::bug("implicit type not resolved").span(root.span)
            )
        }
        _ => {
            error!("{:#?}", root);
            cx.unimp_msg("type analysis of", root)
        }
    }
}

/// Get the cast type of a node.
#[moore_derive::query]
pub(crate) fn cast_type<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> Option<CastType<'a>> {
    let hir = match cx.hir_of(node_id) {
        Ok(x) => x,
        Err(()) => return Some(ty::UnpackedType::make_error().into()),
    };
    match hir {
        HirNode::Expr(e) => Some(cast_expr_type(cx, e, env)),
        _ => None,
    }
}

/// Get the cast type of an expression.
fn cast_expr_type<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &'gcx hir::Expr,
    env: ParamEnv,
) -> CastType<'gcx> {
    let cast = cast_expr_type_inner(cx, expr, env);
    if cx.sess().has_verbosity(Verbosity::CASTS) && !cast.is_error() && !cast.casts.is_empty() {
        let mut d =
            DiagBuilder2::note(format!("cast: `{}` to `{}`", cast.init, cast.ty)).span(expr.span);
        for (op, ty) in &cast.casts {
            let msg = match *op {
                CastOp::PackSBVT => format!("pack as simple bit vector type `{}`", ty),
                CastOp::UnpackSBVT => format!("unpack simple bit vector type as `{}`", ty),
                CastOp::Bool => format!("cast to boolean `{}`", ty),
                CastOp::Sign(sign) => format!("sign cast to {} type `{}`", sign, ty),
                CastOp::Range(_, signed) => format!(
                    "{} size cast to `{}`",
                    match signed {
                        true => "sign-extended",
                        false => "zero-extended",
                    },
                    ty
                ),
                CastOp::Domain(domain) => format!(
                    "cast to {} `{}`",
                    match domain {
                        ty::Domain::TwoValued => "two-valued",
                        ty::Domain::FourValued => "four-valued",
                    },
                    ty
                ),
            };
            d = d.add_note(msg);
        }
        cx.emit(d);
    }
    cast
}

/// Get the cast type of an expression.
fn cast_expr_type_inner<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &'gcx hir::Expr,
    env: ParamEnv,
) -> CastType<'gcx> {
    trace!(
        "Computing cast type of `{}` (line {})",
        expr.span().extract(),
        expr.span().begin().human_line()
    );

    // Determine the inferred type and type context of the expression.
    let inferred = cx.type_of_expr(Ref(expr), env);
    let context = cx.type_context(expr.id, env);
    trace!("  Inferred: {}", inferred);
    trace!(
        "  Context:  {}",
        context
            .map(|c| c.to_string())
            .unwrap_or_else(|| "<none>".to_string())
    );

    // No need to cast lvalues.
    if expr_is_lvalue(cx, expr.id, env) {
        trace!("  Not casting lvalue");
        return inferred.into();
    }

    // If there is no type context which we have to cast to, return.
    let context = match context {
        Some(c) => c,
        None => return inferred.into(),
    };

    // If any of the inputs are tombstones, return.
    if inferred.is_error() || context.is_error() {
        trace!("  Aborting due to error");
        return inferred.into();
    }

    // If types already match, return.
    if let TypeContext2::Type(ty) = context {
        if ty.is_strictly_identical(inferred) {
            trace!("  Already identical");
            return inferred.into();
        }
    }

    // Begin the cast sequence.
    let mut cast = CastType {
        init: inferred,
        ty: inferred,
        casts: vec![],
    };

    // Cast the expression to a simple bit vector type.
    let inferred_sbvt = match inferred.get_simple_bit_vector() {
        Some(ty) => {
            let ty = ty.forget();
            if !inferred.is_simple_bit_vector() {
                trace!("  Packing SBVT");
                cast.add_cast(CastOp::PackSBVT, ty.to_unpacked(cx));
            }
            ty
        }
        None => {
            cx.emit(
                DiagBuilder2::error(format!(
                    "cannot cast a value of type `{}` to `{}`",
                    inferred, context
                ))
                .span(expr.span)
                .add_note(format!(
                    "`{}` has no simple bit-vector type representation",
                    inferred
                )),
            );
            error!("Cast chain thus far: {}", cast);
            return ty::UnpackedType::make_error().into();
        }
    };
    if cast.is_error() {
        trace!("  Aborting due to error");
        return cast;
    }
    trace!("  Mapped `{}` to SBVT `{}`", inferred, inferred_sbvt);

    // Cast the SBVT to a boolean.
    let context = match context {
        TypeContext2::Bool => {
            trace!("  Casting to bool ({})", context.ty());
            cast.add_cast(CastOp::Bool, context.ty());
            return cast;
        }
        TypeContext2::Type(ty) => ty,
    };

    // Cast the context type to an SBVT.
    let context_sbvt = match context.get_simple_bit_vector() {
        Some(ty) => ty.forget(),
        None => {
            cx.emit(
                DiagBuilder2::error(format!("cannot cast to a value of type `{}`", context))
                    .span(expr.span)
                    .add_note(format!(
                        "`{}` has no simple bit-vector type representation",
                        context
                    )),
            );
            error!("Cast chain thus far: {}", cast);
            return ty::UnpackedType::make_error().into();
        }
    };
    trace!("  Mapped `{}` to SBVT `{}`", context, context_sbvt);

    // Change size.
    //
    // For example: `bit [7:0]` to `bit [2:0]`.
    let inferred_sbvt = if inferred_sbvt.size != context_sbvt.size {
        trace!(
            "  Casting size from {} to {}",
            inferred_sbvt.range(),
            context_sbvt.range()
        );
        let ty = inferred_sbvt.change_size(context_sbvt.size);
        cast.add_cast(
            CastOp::Range(context_sbvt.range(), inferred_sbvt.is_signed()),
            ty.to_unpacked(cx),
        );
        ty
    } else {
        inferred_sbvt
    };
    if cast.is_error() {
        trace!("  Aborting due to error");
        return cast;
    }

    // Change sign.
    //
    // For example: `bit` to `bit signed`, or `bit signed` to `bit unsigned`.
    let inferred_sbvt = if inferred_sbvt.sign != context_sbvt.sign {
        trace!(
            "  Casting sign from {:?} to {:?}",
            inferred_sbvt.sign,
            context_sbvt.sign
        );
        let ty = inferred_sbvt.change_sign(context_sbvt.sign);
        cast.add_cast(CastOp::Sign(context_sbvt.sign), ty.to_unpacked(cx));
        ty
    } else {
        inferred_sbvt
    };
    if cast.is_error() {
        trace!("  Aborting due to error");
        return cast;
    }

    // Change domain.
    //
    // For example: `bit` to `logic`, or `logic` to `bit`.
    let inferred_sbvt = if inferred_sbvt.domain != context_sbvt.domain {
        trace!(
            "  Casting domain from {:?} to {:?}",
            inferred_sbvt.domain,
            context_sbvt.domain
        );
        let ty = inferred_sbvt.change_domain(context_sbvt.domain);
        cast.add_cast(CastOp::Domain(context_sbvt.domain), ty.to_unpacked(cx));
        ty
    } else {
        inferred_sbvt
    };
    if cast.is_error() {
        trace!("  Aborting due to error");
        return cast;
    }

    // At this point the SBVTs must match.
    assert!(
        inferred_sbvt.is_identical(&context_sbvt),
        "SBVTs `{}` and `{}` must match at this point",
        inferred_sbvt,
        context_sbvt
    );

    // Unpack the simple bit vector as complex type.
    if !context.is_simple_bit_vector() {
        trace!("  Unpacking SBVT");
        cast.add_cast(CastOp::UnpackSBVT, context);
    }
    if cast.is_error() {
        trace!("  Aborting due to error");
        return cast;
    }

    // If types match now, we're good.
    if context.is_strictly_identical(cast.ty) {
        trace!("  Cast complete");
        return cast;
    }

    // If we arrive here, casting failed.
    let mut d = DiagBuilder2::error(format!(
        "cannot cast a value of type `{}` to `{}`",
        inferred, context
    ))
    .span(expr.span);
    if !cast.casts.is_empty() {
        d = d.add_note(format!(
            "`{}` can be cast to an intermediate `{}`, but",
            inferred, cast.ty
        ));
        d = d.add_note(format!(
            "`{}` cannot be cast to the final `{}`",
            cast.ty, context
        ));
    }
    cx.emit(d);
    error!("Inferred type: {:?}", inferred);
    error!("Context type: {:?}", context);
    error!("Cast chain thus far: {}", cast);
    ty::UnpackedType::make_error().into()
}

/// Get the self-determined type of a node.
#[moore_derive::query]
pub(crate) fn self_determined_type<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> Option<&'a UnpackedType<'a>> {
    let hir = match cx.hir_of(node_id) {
        Ok(x) => x,
        Err(()) => return Some(UnpackedType::make_error()),
    };
    match hir {
        HirNode::Expr(e) => self_determined_expr_type(cx, e, env),
        _ => None,
    }
}

/// Require a node to have a self-determined type.
///
/// Emits an error if the node has no self-determined type.
#[moore_derive::query]
pub(crate) fn need_self_determined_type<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    match cx.self_determined_type(node_id, env) {
        Some(ty) => ty,
        None => {
            let extract = cx.span(node_id).extract();
            let desc = cx
                .ast_of(node_id)
                .map(|x| x.desc_full())
                .unwrap_or_else(|_| format!("`{}`", extract));
            cx.emit(
                DiagBuilder2::error(format!("{} has no self-determined type", desc))
                    .span(cx.span(node_id))
                    .add_note(format!(
                        "The type of {} must be inferred from context, but the location where you \
                         used it does not provide such information.",
                        desc
                    ))
                    .add_note(format!("Try a cast: `T'({})`", extract)),
            );
            UnpackedType::make_error()
        }
    }
}

/// Get the self-determined type of an expression.
fn self_determined_expr_type<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &'gcx hir::Expr,
    env: ParamEnv,
) -> Option<&'gcx UnpackedType<'gcx>> {
    match expr.kind {
        // Unsized constants fall back to their single bit equivalent.
        hir::ExprKind::UnsizedConst(_) => Some(UnpackedType::make_logic()),

        // Sized integer constants have a well-defined type.
        hir::ExprKind::IntConst {
            width,
            signed,
            ref special_bits,
            ..
        } => Some(
            SbvType::nice(
                match special_bits.any() {
                    true => ty::Domain::FourValued,
                    false => ty::Domain::TwoValued,
                },
                if signed {
                    ty::Sign::Signed
                } else {
                    ty::Sign::Unsigned
                },
                width,
            )
            .to_unpacked(cx),
        ),

        // Time constants are of time type.
        hir::ExprKind::TimeConst(_) => Some(UnpackedType::make_time()),

        // String literals are of string type.
        hir::ExprKind::StringConst(_) => Some(
            ty::PackedType::make_dims(
                cx,
                ty::IntAtomType::Byte,
                vec![ty::PackedDim::Range(ty::Range {
                    size: 1,
                    dir: ty::RangeDir::Down,
                    offset: 0,
                })],
            )
            .to_unpacked(cx),
        ),

        // Identifiers and scoped identifiers inherit their type from the bound
        // node.
        hir::ExprKind::Ident(_) | hir::ExprKind::Scope(..) => Some(
            cx.resolve_node(expr.id, env)
                .and_then(|x| cx.type_of(x, env))
                .map(|ty| UnpackedType::from_legacy(cx, ty))
                .unwrap_or(UnpackedType::make_error()),
        ),

        // Concatenation yields an unsigned logic vector whose bit width is the
        // sum of the simple bit vector types of each argument.
        //
        // See §11.8.1 "Rules for expression types".
        hir::ExprKind::Concat(repeat, ref exprs) => {
            let mut failed = false;

            // Determine the cumulative width of all fields.
            let mut bit_width = 0;
            let mut domain = ty::Domain::TwoValued;
            for &expr in exprs {
                let ty = cx.need_self_determined_type(expr, env);
                if ty.is_error() {
                    failed = true;
                    continue;
                }
                if ty.domain() == ty::Domain::FourValued {
                    domain = ty::Domain::FourValued;
                }
                match ty.get_simple_bit_vector() {
                    Some(sbv) => bit_width += sbv.size,
                    None => {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "cannot concatenate a value of type `{}`",
                                ty
                            ))
                            .span(cx.span(expr))
                            .add_note(format!(
                                "`{}` has no simple bit-vector type representation",
                                ty
                            )),
                        );
                        failed = true;
                        continue;
                    }
                }
            }

            // Determine the repetition factor.
            let repeat = match repeat {
                Some(repeat) => match cx.constant_int_value_of(repeat, env) {
                    Ok(r) => r.to_usize().unwrap(),
                    Err(()) => {
                        failed = true;
                        0
                    }
                },
                None => 1,
            };

            // Package up the result.
            if failed {
                Some(UnpackedType::make_error())
            } else {
                Some(SbvType::new(domain, Sign::Unsigned, repeat * bit_width).to_unpacked(cx))
            }
        }

        // Casts trivially evaluate to the cast type.
        hir::ExprKind::Cast(ty, _) => Some(
            cx.map_to_type(ty, env)
                .map(|ty| UnpackedType::from_legacy(cx, ty))
                .unwrap_or(UnpackedType::make_error()),
        ),

        // Sign casts trivially evaluate to the sign-converted inner type.
        hir::ExprKind::CastSign(sign, arg) => {
            Some(self_determined_sign_cast_type(cx, sign.value, arg, env))
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::Signed(arg)) => {
            Some(self_determined_sign_cast_type(cx, Sign::Signed, arg, env))
        }
        hir::ExprKind::Builtin(hir::BuiltinCall::Unsigned(arg)) => {
            Some(self_determined_sign_cast_type(cx, Sign::Unsigned, arg, env))
        }

        // Sign casts trivially evaluate to the size-converted inner type.
        hir::ExprKind::CastSize(size, arg) => {
            // Determine the actual size.
            let size = match cx.constant_int_value_of(size, env) {
                Ok(r) => r.to_usize().unwrap(),
                Err(_) => {
                    return Some(UnpackedType::make_error());
                }
            };

            // Map the inner type to a simple bit vector.
            let inner_ty = cx.need_self_determined_type(arg, env);
            if inner_ty.is_error() {
                return Some(UnpackedType::make_error());
            }
            let sbv = match inner_ty.get_simple_bit_vector() {
                Some(sbv) => sbv,
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "cannot size-cast a value of type `{}`",
                            inner_ty
                        ))
                        .span(cx.span(arg))
                        .add_note(format!(
                            "`{}` has no simple bit-vector type representation",
                            inner_ty
                        )),
                    );
                    return Some(UnpackedType::make_error());
                }
            };

            // Change the size and return the new type.
            Some(sbv.change_size(size).to_unpacked(cx))
        }

        // The `inside` expression evaluates to a boolean.
        hir::ExprKind::Inside(..) => Some(UnpackedType::make_logic()),

        // Most builtin functions evaluate to the integer type.
        hir::ExprKind::Builtin(hir::BuiltinCall::Unsupported)
        | hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(_))
        | hir::ExprKind::Builtin(hir::BuiltinCall::Bits(_)) => {
            Some(PackedType::make(cx, ty::IntAtomType::Int).to_unpacked(cx))
        }

        // Member field accesses resolve to the type of the member.
        hir::ExprKind::Field(..) => Some(
            cx.resolve_field_access(expr.id, env)
                .and_then(|(_, _, field_id)| cx.type_of(field_id.id(), env))
                .map(|ty| UnpackedType::from_legacy(cx, ty))
                .unwrap_or(UnpackedType::make_error()),
        ),

        // Bit- and part-select expressions
        hir::ExprKind::Index(target, mode) => {
            // Determine the width of the accessed slice. `None` indicates a
            // single element access, which needs to be treated differently in
            // some cases.
            let width = || -> Result<_> {
                Ok(match mode {
                    hir::IndexMode::One(..) => None,
                    hir::IndexMode::Many(ast::RangeMode::RelativeUp, _, delta)
                    | hir::IndexMode::Many(ast::RangeMode::RelativeDown, _, delta) => {
                        Some(cx.constant_int_value_of(delta, env)?.to_usize().unwrap())
                    }
                    hir::IndexMode::Many(ast::RangeMode::Absolute, lhs, rhs) => {
                        let lhs_int = cx.constant_int_value_of(lhs, env)?;
                        let rhs_int = cx.constant_int_value_of(rhs, env)?;
                        let length = (lhs_int - rhs_int).abs() + BigInt::one();
                        Some(length.to_usize().unwrap())
                    }
                })
            }();
            let width = match width {
                Ok(w) => w,
                Err(_) => return Some(UnpackedType::make_error()),
            };

            // Determine the target type.
            let target_ty = cx.need_operation_type(expr.id, env);
            if target_ty.is_error() {
                return Some(target_ty);
            }

            // If we are selecting a slice (width not None), the result type is
            // the array, but with the outermost array dimension changed. If we
            // are selecting a bit, the result is the type with the selected
            // dimension removed. Also, distinguish arrays from SBVTs.
            let result = if let Some(dim) = target_ty.outermost_dim() {
                // We are selecting into an array.
                match width {
                    Some(width) => {
                        // We are selecting an array slice.
                        let range = ty::Range::with_size(width);
                        target_ty.replace_dim(
                            cx,
                            match dim {
                                ty::Dim::Packed(..) => ty::Dim::Packed(range.into()),
                                ty::Dim::Unpacked(..) => ty::Dim::Unpacked(range.into()),
                            },
                        )
                    }
                    None => {
                        // We are selecting an array index.
                        target_ty.pop_dim(cx).unwrap()
                    }
                }
            } else {
                // We are not selecting into an array.
                let sbvt = target_ty.simple_bit_vector(cx, cx.span(target));
                match width {
                    Some(width) => {
                        // We are selecting a bit slice.
                        sbvt.change_size(width).to_unpacked(cx)
                    }
                    None => {
                        // We are selecting a bit index.
                        let mut sbvt = sbvt.change_size(1);
                        sbvt.size_explicit = false;
                        sbvt.to_unpacked(cx)
                    }
                }
            };
            Some(result)
        }

        // Some unary operators have a fully self-determined type.
        hir::ExprKind::Unary(op, arg) => match op {
            // Handle the self-determined cases.
            hir::UnaryOp::LogicNot => Some(UnpackedType::make_logic()),
            hir::UnaryOp::RedAnd
            | hir::UnaryOp::RedOr
            | hir::UnaryOp::RedXor
            | hir::UnaryOp::RedNand
            | hir::UnaryOp::RedNor
            | hir::UnaryOp::RedXnor => cx.self_determined_type(arg, env).map(|ty| {
                PackedType::make(
                    cx,
                    match ty.domain() {
                        Domain::TwoValued => ty::IntVecType::Bit,
                        Domain::FourValued => ty::IntVecType::Logic,
                    },
                )
                .to_unpacked(cx)
            }),

            // For all other cases we try to infer the argument's type.
            hir::UnaryOp::Neg
            | hir::UnaryOp::Pos
            | hir::UnaryOp::BitNot
            | hir::UnaryOp::PreInc
            | hir::UnaryOp::PreDec
            | hir::UnaryOp::PostInc
            | hir::UnaryOp::PostDec => {
                unify_operator_types(cx, env, cx.self_determined_type(arg, env).into_iter())
            }
        },

        // Some binary operators have a fully self-determined type.
        hir::ExprKind::Binary(op, lhs, rhs) => match op {
            // Handle the self-determined cases.
            hir::BinaryOp::Eq
            | hir::BinaryOp::Neq
            | hir::BinaryOp::Lt
            | hir::BinaryOp::Leq
            | hir::BinaryOp::Gt
            | hir::BinaryOp::Geq
            | hir::BinaryOp::LogicAnd
            | hir::BinaryOp::LogicOr => Some(UnpackedType::make_logic()),

            // For all other cases we try to infer a type based on the maximum
            // over the operand's self-determined types.
            hir::BinaryOp::Add
            | hir::BinaryOp::Sub
            | hir::BinaryOp::Mul
            | hir::BinaryOp::Div
            | hir::BinaryOp::Mod
            | hir::BinaryOp::BitAnd
            | hir::BinaryOp::BitNand
            | hir::BinaryOp::BitOr
            | hir::BinaryOp::BitNor
            | hir::BinaryOp::BitXor
            | hir::BinaryOp::BitXnor => {
                let tlhs = cx.self_determined_type(lhs, env);
                let trhs = cx.self_determined_type(rhs, env);
                unify_operator_types(cx, env, tlhs.into_iter().chain(trhs.into_iter()))
            }

            // Exponentiation and shifts operate on the left-hand side type.
            hir::BinaryOp::Pow
            | hir::BinaryOp::LogicShL
            | hir::BinaryOp::LogicShR
            | hir::BinaryOp::ArithShL
            | hir::BinaryOp::ArithShR => cx.self_determined_type(lhs, env),
        },

        // Ternary operators infer a type based on the maximum over the
        // operand's self-determined types.
        hir::ExprKind::Ternary(_, lhs, rhs) => {
            let tlhs = cx.self_determined_type(lhs, env);
            let trhs = cx.self_determined_type(rhs, env);
            unify_operator_types(cx, env, tlhs.into_iter().chain(trhs.into_iter()))
        }

        // Function calls resolve to the function's return type.
        hir::ExprKind::FunctionCall(target, _) => Some(
            cx.hir_of(target)
                .and_then(|hir| {
                    let hir = match hir {
                        HirNode::Subroutine(s) => s,
                        _ => unreachable!(),
                    };
                    match hir.retty {
                        Some(retty_id) => cx
                            .map_to_type(retty_id, env)
                            .map(|ty| UnpackedType::from_legacy(cx, ty)),
                        None => Ok(UnpackedType::make_void()),
                    }
                })
                .unwrap_or(UnpackedType::make_error()),
        ),

        _ => None,
    }
}

fn self_determined_sign_cast_type<'gcx>(
    cx: &impl Context<'gcx>,
    sign: Sign,
    arg: NodeId,
    env: ParamEnv,
) -> &'gcx UnpackedType<'gcx> {
    // Map the inner type to a simple bit vector.
    let ty = cx.need_self_determined_type(arg, env);
    if ty.is_error() {
        return UnpackedType::make_error();
    }
    let sbv = match ty.get_simple_bit_vector() {
        Some(sbv) => sbv,
        None => {
            cx.emit(
                DiagBuilder2::error(format!("cannot sign-cast a value of type `{}`", ty))
                    .span(cx.span(arg))
                    .add_note(format!(
                        "`{}` has no simple bit-vector type representation",
                        ty
                    )),
            );
            return UnpackedType::make_error();
        }
    };

    // Change sign and return the new type.
    sbv.change_sign(sign).to_unpacked(cx)
}

/// Get the operation type of an expression.
#[moore_derive::query]
pub(crate) fn operation_type<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> Option<&'a UnpackedType<'a>> {
    let hir = match cx.hir_of(node_id) {
        Ok(x) => x,
        Err(_) => return Some(UnpackedType::make_error()),
    };
    let expr = match hir {
        HirNode::Expr(x) => x,
        _ => return None,
    };
    match expr.kind {
        // Unary operators all have an inherent operation type.
        hir::ExprKind::Unary(op, arg) => {
            let ty = match op {
                // Most operators operate on the maximum bitwidth given by their
                // argument (self-determined type) and the type context.
                hir::UnaryOp::RedAnd
                | hir::UnaryOp::RedOr
                | hir::UnaryOp::RedXor
                | hir::UnaryOp::RedNand
                | hir::UnaryOp::RedNor
                | hir::UnaryOp::RedXnor
                | hir::UnaryOp::Neg
                | hir::UnaryOp::Pos
                | hir::UnaryOp::BitNot
                | hir::UnaryOp::PreInc
                | hir::UnaryOp::PreDec
                | hir::UnaryOp::PostInc
                | hir::UnaryOp::PostDec => {
                    let tc = cx.type_context(node_id, env).map(|x| x.ty());
                    let targ = cx.self_determined_type(arg, env);
                    unify_operator_types(cx, env, tc.into_iter().chain(targ.into_iter()))
                }

                // Handle the self-determined cases.
                hir::UnaryOp::LogicNot => Some(UnpackedType::make_logic()),
            };
            if ty.is_none() {
                cx.emit(
                    DiagBuilder2::error(format!("type of {} cannot be inferred", expr.desc_full()))
                        .span(expr.human_span())
                        .add_note(
                            "The operand does not have a self-determined type, and the type \
                             cannot be inferred from the context.",
                        )
                        .add_note(format!("Try a cast: `T'({})`", expr.span().extract())),
                );
                Some(UnpackedType::make_error())
            } else {
                ty
            }
        }

        // Binary operators all have an inherent operation type.
        hir::ExprKind::Binary(op, lhs, rhs) => {
            let ty = match op {
                // Most arithmetic operators and comparisons operate on the
                // maximum bitwidth given by their arguments (self-determined
                // type) and the type context.
                hir::BinaryOp::Add
                | hir::BinaryOp::Sub
                | hir::BinaryOp::Mul
                | hir::BinaryOp::Div
                | hir::BinaryOp::Mod
                | hir::BinaryOp::BitAnd
                | hir::BinaryOp::BitNand
                | hir::BinaryOp::BitOr
                | hir::BinaryOp::BitNor
                | hir::BinaryOp::BitXor
                | hir::BinaryOp::BitXnor => {
                    let tc = cx.type_context(node_id, env).map(|x| x.ty());
                    let tlhs = cx.self_determined_type(lhs, env);
                    let trhs = cx.self_determined_type(rhs, env);
                    unify_operator_types(
                        cx,
                        env,
                        tc.into_iter()
                            .chain(tlhs.into_iter())
                            .chain(trhs.into_iter()),
                    )
                }

                // Comparison operations do not consider their type context, but
                // use the maximum bit width of the operands.
                hir::BinaryOp::Eq
                | hir::BinaryOp::Neq
                | hir::BinaryOp::Lt
                | hir::BinaryOp::Leq
                | hir::BinaryOp::Gt
                | hir::BinaryOp::Geq => {
                    let tlhs = cx.self_determined_type(lhs, env);
                    let trhs = cx.self_determined_type(rhs, env);
                    unify_operator_types(cx, env, tlhs.into_iter().chain(trhs.into_iter()))
                }

                // The boolean logic operators simply operate on bits.
                hir::BinaryOp::LogicAnd | hir::BinaryOp::LogicOr => {
                    Some(UnpackedType::make_logic())
                }

                // Exponentiation and shifts operate on the left-hand side type.
                hir::BinaryOp::Pow
                | hir::BinaryOp::LogicShL
                | hir::BinaryOp::LogicShR
                | hir::BinaryOp::ArithShL
                | hir::BinaryOp::ArithShR => {
                    let tc = cx.type_context(node_id, env).map(|x| x.ty());
                    let sdt = cx.self_determined_type(lhs, env);
                    unify_operator_types(cx, env, tc.into_iter().chain(sdt.into_iter()))
                }
            };
            if ty.is_none() {
                cx.emit(
                    DiagBuilder2::error(format!("type of {} cannot be inferred", expr.desc_full()))
                        .span(expr.human_span())
                        .add_note(
                            "Neither of the operands has a self-determined type, and the type \
                             cannot be inferred from the context.",
                        )
                        .add_note(format!("Try a cast: `T'({})`", expr.span().extract())),
                );
                Some(UnpackedType::make_error())
            } else {
                ty
            }
        }

        // Ternary operators operate on the maximum bitwidth given by their
        // arguments (self-determined type) and the type context.
        hir::ExprKind::Ternary(_, lhs, rhs) => {
            let tc = cx.type_context(node_id, env).map(|x| x.ty());
            let tlhs = cx.self_determined_type(lhs, env);
            let trhs = cx.self_determined_type(rhs, env);
            unify_operator_types(
                cx,
                env,
                tc.into_iter()
                    .chain(tlhs.into_iter())
                    .chain(trhs.into_iter()),
            )
        }

        // The inside expression uses an operation type for its comparisons. It
        // is determined in the same way as for comparisons.
        hir::ExprKind::Inside(lhs, ref ranges) => {
            let tlhs = cx.self_determined_type(lhs, env);
            let tranges = ranges.iter().flat_map(|r| {
                let (a, b) = match r.value {
                    hir::InsideRange::Single(rhs) => (cx.self_determined_type(rhs, env), None),
                    hir::InsideRange::Range(lo, hi) => (
                        cx.self_determined_type(lo, env),
                        cx.self_determined_type(hi, env),
                    ),
                };
                a.into_iter().chain(b.into_iter())
            });
            unify_operator_types(cx, env, tlhs.into_iter().chain(tranges))
        }

        // Bit- and part-select expressions map their target to an internal type
        // that is suitable for indexing, then operate on that.
        hir::ExprKind::Index(target, _mode) => {
            // Determine the target type.
            let target_ty = cx.need_self_determined_type(target, env);
            if target_ty.is_error() {
                return Some(target_ty);
            }

            // We are either indexing into an array, in which case the operation
            // type is simply that array, or into anything else, in which case
            // the target is cast to an SBVT for indexing.
            if let Some(_dim) = target_ty.outermost_dim() {
                Some(target_ty)
            } else {
                match target_ty.get_simple_bit_vector() {
                    Some(sbvt) => Some(sbvt.forget().to_unpacked(cx)),
                    None => {
                        cx.emit(
                            DiagBuilder2::error(
                                format!("cannot index into a value of type `{}`", target_ty),
                            )
                            .span(expr.span)
                            .add_note(format!(
                                "`{}` must be an array or have a simple bit-vector type representation",
                                target_ty
                            )),
                        );
                        Some(UnpackedType::make_error())
                    }
                }
            }
        }

        _ => None,
    }
}

/// Determine the bit length, sign, and value domain of the types that influence
/// an expression.
fn unify_operator_types<'gcx>(
    cx: &impl Context<'gcx>,
    _env: ParamEnv,
    types: impl Iterator<Item = &'gcx UnpackedType<'gcx>>,
) -> Option<&'gcx UnpackedType<'gcx>> {
    // Map the iterator to a sequence of sign, domain, and bit width tuples.
    let inner: Vec<_> = types.flat_map(|ty| ty.get_simple_bit_vector()).collect();

    // Determine the maximum width, sign, and domain.
    let width: Option<usize> = inner.iter().map(|&sbv| sbv.size).max();
    let sign = match inner.iter().all(|&sbv| sbv.is_signed()) {
        true => Sign::Signed,
        false => Sign::Unsigned,
    };
    let domain = match inner.iter().all(|&sbv| sbv.domain == Domain::TwoValued) {
        true => Domain::TwoValued,
        false => Domain::FourValued,
    };

    // Construct the type.
    width.map(|w| SbvType::nice(domain, sign, w).to_unpacked(cx))
}

/// Require a node to have an operation type.
///
/// Emits an error if the node has no operation type.
#[moore_derive::query]
pub(crate) fn need_operation_type<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    match cx.operation_type(node_id, env) {
        Some(x) => x,
        None => {
            let span = cx.span(node_id);
            cx.emit(
                DiagBuilder2::bug(format!("`{}` has no operation type", span.extract())).span(span),
            );
            UnpackedType::make_error()
        }
    }
}

/// Get the type context of a node.
#[moore_derive::query]
pub(crate) fn type_context<'a>(
    cx: &impl Context<'a>,
    onto: NodeId,
    env: ParamEnv,
) -> Option<TypeContext2<'a>> {
    let hir = match cx.hir_of(cx.parent_node_id(onto).unwrap()) {
        Ok(x) => x,
        Err(()) => return None,
    };
    match hir {
        HirNode::Expr(e) => type_context_imposed_by_expr(cx, onto, e, env),
        HirNode::Stmt(s) => type_context_imposed_by_stmt(cx, onto, s, env),
        HirNode::Assign(a) => {
            if a.lhs == onto {
                cx.self_determined_type(a.rhs, env).map(Into::into)
            } else if a.rhs == onto {
                cx.self_determined_type(a.lhs, env).map(Into::into)
            } else {
                None
            }
        }
        HirNode::IntPort(hir::IntPort { data: Some(v), .. })
            if v.default == Some(onto) && is_explicit_type(cx, v.ty).unwrap_or(false) =>
        {
            Some(
                cx.map_to_type(v.ty, env)
                    .map(|ty| UnpackedType::from_legacy(cx, ty))
                    .unwrap_or(UnpackedType::make_error())
                    .into(),
            )
        }
        HirNode::VarDecl(v)
            if v.init == Some(onto) && is_explicit_type(cx, v.ty).unwrap_or(false) =>
        {
            Some(
                cx.map_to_type(v.ty, env)
                    .map(|ty| UnpackedType::from_legacy(cx, ty))
                    .unwrap_or(UnpackedType::make_error())
                    .into(),
            )
        }
        HirNode::ValueParam(v)
            if v.default == Some(onto) && is_explicit_type(cx, v.ty).unwrap_or(false) =>
        {
            Some(
                cx.map_to_type(v.ty, env)
                    .map(|ty| UnpackedType::from_legacy(cx, ty))
                    .unwrap_or(UnpackedType::make_error())
                    .into(),
            )
        }
        HirNode::Inst(inst) => {
            let details = cx.inst_details(inst.id.env(env)).ok()?;
            details
                .ports
                .reverse_find(onto)
                .and_then(|id| cx.type_of(id, details.inner_env).ok())
                .map(|ty| UnpackedType::from_legacy(cx, ty))
                .map(Into::into)
        }
        HirNode::InstTarget(inst) => {
            let details = cx.inst_target_details(inst.id.env(env)).ok()?;
            details
                .params
                .reverse_find_value(onto)
                .and_then(|param_id| cx.type_of(param_id, details.inner_env).ok())
                .map(|ty| UnpackedType::from_legacy(cx, ty))
                .map(Into::into)
        }
        _ => None,
    }
}

/// Get the type context of a node.
#[moore_derive::query]
pub(crate) fn need_type_context<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> TypeContext2<'a> {
    match cx.type_context(node_id, env) {
        Some(ty) => ty,
        None => {
            let extract = cx.span(node_id).extract();
            let desc = cx
                .ast_of(node_id)
                .map(|x| x.desc_full())
                .unwrap_or_else(|_| format!("`{}`", extract));
            cx.emit(
                DiagBuilder2::error(format!("type of {} cannot be inferred from context", desc))
                    .span(cx.span(node_id))
                    .add_note(format!(
                        "The type of {} must be inferred from context, but the location where you \
                         used it does not provide such information.",
                        desc
                    ))
                    .add_note(format!("Try a cast: `T'({})`", extract)),
            );
            UnpackedType::make_error().into()
        }
    }
}

/// A type context imposed by a node's surroundings.
///
/// This is used to treat things such as assignment-like contexts.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum TypeContext<'a> {
    /// The surroundings impose a regular type.
    Type(Type<'a>),
    /// The surroundings ask for implicit boolean mapping (not truncation).
    Bool,
}

impl<'a> TypeContext<'a> {
    /// Convert the type context to an actual type.
    ///
    /// This resolves implicit boolean casts to the `logic` type.
    pub fn ty(&self) -> Type<'a> {
        match *self {
            TypeContext::Type(t) => t,
            TypeContext::Bool => &ty::LOGIC_TYPE,
        }
    }

    /// Check if the type context is a tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            TypeContext::Type(t) => t.is_error(),
            TypeContext::Bool => false,
        }
    }
}

impl<'a> From<Type<'a>> for TypeContext<'a> {
    fn from(ty: Type<'a>) -> Self {
        TypeContext::Type(ty)
    }
}

impl std::fmt::Display for TypeContext<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TypeContext::Type(t) => write!(f, "{}", t),
            TypeContext::Bool => write!(f, "<bool>"),
        }
    }
}

/// A type context imposed by a node's surroundings.
///
/// This is used to treat things such as assignment-like contexts.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum TypeContext2<'a> {
    /// The surroundings impose a regular type.
    Type(&'a ty::UnpackedType<'a>),
    /// The surroundings ask for implicit boolean mapping (not truncation).
    Bool,
}

impl<'a> TypeContext2<'a> {
    /// Convert the type context to an actual type.
    ///
    /// This resolves implicit boolean casts to the `logic` type.
    pub fn ty(&self) -> &'a ty::UnpackedType<'a> {
        match *self {
            TypeContext2::Type(t) => t,
            TypeContext2::Bool => ty::UnpackedType::make_logic(),
        }
    }

    /// Check if the type context is a tombstone.
    pub fn is_error(&self) -> bool {
        match self {
            TypeContext2::Type(t) => t.is_error(),
            TypeContext2::Bool => false,
        }
    }
}

impl<'a> From<&'a ty::UnpackedType<'a>> for TypeContext2<'a> {
    fn from(ty: &'a ty::UnpackedType<'a>) -> Self {
        TypeContext2::Type(ty)
    }
}

impl std::fmt::Display for TypeContext2<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TypeContext2::Type(t) => write!(f, "{}", t),
            TypeContext2::Bool => write!(f, "<bool>"),
        }
    }
}

/// Get the type context imposed by an expression.
///
/// Determine the type context `expr` imposes on `onto`.
fn type_context_imposed_by_expr<'gcx>(
    cx: &impl Context<'gcx>,
    onto: NodeId,
    expr: &'gcx hir::Expr,
    env: ParamEnv,
) -> Option<TypeContext2<'gcx>> {
    match expr.kind {
        hir::ExprKind::Unary(op, _) => match op {
            // The unary operators whose output type does not depend on the
            // operands also do not impose a type context on their operands.
            hir::UnaryOp::RedAnd
            | hir::UnaryOp::RedOr
            | hir::UnaryOp::RedXor
            | hir::UnaryOp::RedNand
            | hir::UnaryOp::RedNor
            | hir::UnaryOp::RedXnor => None,

            // The logic operators require boolean arguments.
            hir::UnaryOp::LogicNot => Some(TypeContext2::Bool),

            // For all other cases we impose our self-determined type as
            // context.
            hir::UnaryOp::Neg
            | hir::UnaryOp::Pos
            | hir::UnaryOp::BitNot
            | hir::UnaryOp::PreInc
            | hir::UnaryOp::PreDec
            | hir::UnaryOp::PostInc
            | hir::UnaryOp::PostDec => Some(cx.need_operation_type(expr.id, env).into()),
        },

        hir::ExprKind::Binary(op, lhs, _) => match op {
            // The logic operators require boolean arguments.
            hir::BinaryOp::LogicAnd | hir::BinaryOp::LogicOr => Some(TypeContext2::Bool),

            // Exponentiation and shifts impose a type context on their left
            // hand side.
            hir::BinaryOp::Pow
            | hir::BinaryOp::LogicShL
            | hir::BinaryOp::LogicShR
            | hir::BinaryOp::ArithShL
            | hir::BinaryOp::ArithShR => {
                if onto == lhs {
                    Some(cx.need_operation_type(expr.id, env).into())
                } else {
                    None
                }
            }

            // For all other cases we impose the operator type.
            hir::BinaryOp::Add
            | hir::BinaryOp::Sub
            | hir::BinaryOp::Mul
            | hir::BinaryOp::Div
            | hir::BinaryOp::Mod
            | hir::BinaryOp::BitAnd
            | hir::BinaryOp::BitNand
            | hir::BinaryOp::BitOr
            | hir::BinaryOp::BitNor
            | hir::BinaryOp::BitXor
            | hir::BinaryOp::BitXnor
            | hir::BinaryOp::Eq
            | hir::BinaryOp::Neq
            | hir::BinaryOp::Lt
            | hir::BinaryOp::Leq
            | hir::BinaryOp::Gt
            | hir::BinaryOp::Geq => Some(cx.need_operation_type(expr.id, env).into()),
        },

        // The ternary operator imposes its operation type onto the true and
        // false expressions.
        hir::ExprKind::Ternary(_, lhs, rhs) if onto == lhs || onto == rhs => {
            Some(cx.need_operation_type(expr.id, env).into())
        }

        // The ternary operator imposes a boolean context on its condition.
        hir::ExprKind::Ternary(cond, _, _) if onto == cond => Some(TypeContext2::Bool),

        // Static casts are *not* assignment-like contexts. See §10.8
        // "Assignment-like contexts". We use a trick here to get the implicit
        // casting logic to do the cast for us: we determine the type of the
        // argument after the cast, then impose that as its type context.
        hir::ExprKind::Builtin(hir::BuiltinCall::Signed(arg))
        | hir::ExprKind::Builtin(hir::BuiltinCall::Unsigned(arg))
        | hir::ExprKind::Cast(_, arg)
        | hir::ExprKind::CastSign(_, arg)
        | hir::ExprKind::CastSize(_, arg)
            if onto == arg =>
        {
            Some(cx.need_self_determined_type(expr.id, env).into())
        }

        // Concatenations require their arguments (including repetition counts)
        // to map to a corresponding SBVT.
        hir::ExprKind::Concat(..) => {
            let ty = cx.need_self_determined_type(onto, env);
            if ty.is_error() {
                return Some(ty.into());
            }
            let sbvt = match ty.get_simple_bit_vector() {
                Some(ty) => ty.to_unpacked(cx),
                None => {
                    cx.emit(
                        DiagBuilder2::error(
                            format!("cannot concatenate a value of type `{}`", ty,),
                        )
                        .span(expr.span)
                        .add_note(format!(
                            "`{}` has no simple bit-vector type representation",
                            ty
                        )),
                    );
                    UnpackedType::make_error()
                }
            };
            Some(sbvt.into())
        }

        // Patterns impose the field types onto their arguments.
        hir::ExprKind::PositionalPattern(ref args) => {
            type_context_imposed_by_positional_pattern(cx, onto, expr, args, 1, env)
        }
        hir::ExprKind::RepeatPattern(count, ref args) if onto != count => {
            // TODO(fschuiki): This is a verbatim copy of code in MIR lowering.
            // This should really go into a pattern analysis struct.
            let const_count = match cx.constant_int_value_of(count, env) {
                Ok(c) => c,
                Err(()) => return Some(UnpackedType::make_error().into()),
            };
            let const_count = match const_count.to_usize() {
                Some(c) => c,
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "repetition count {} is outside copable range",
                            const_count,
                        ))
                        .span(cx.span(count)),
                    );
                    return Some(UnpackedType::make_error().into());
                }
            };
            type_context_imposed_by_positional_pattern(cx, onto, expr, args, const_count, env)
        }

        // The `inside` expression imposes its operation type as type context.
        hir::ExprKind::Inside(..) => Some(cx.need_operation_type(expr.id, env).into()),

        // Bit- and part-select expressions impose their operation type as type
        // context.
        hir::ExprKind::Index(target, _) if onto == target => {
            let opty = cx.need_operation_type(expr.id, env);
            debug!(
                "Imposing opty `{}` on `{}`",
                opty,
                cx.span(target).extract()
            );
            Some(opty.into())
        }

        _ => None,
    }
}

fn type_context_imposed_by_positional_pattern<'gcx>(
    cx: &impl Context<'gcx>,
    onto: NodeId,
    expr: &'gcx hir::Expr,
    args: &[NodeId],
    repeat: usize,
    env: ParamEnv,
) -> Option<TypeContext2<'gcx>> {
    let index = args.iter().position(|&n| n == onto)?;
    let ty = cx.need_type_context(expr.id, env).ty();
    if ty.is_error() {
        return Some(UnpackedType::make_error().into());
    }
    let legacy = ty.to_legacy(cx);
    trace!(
        "Pattern `{}` has type `{}`, legacy type is `{}`",
        cx.span(expr.id).extract(),
        ty,
        legacy
    );
    match *legacy.resolve_name() {
        TypeKind::PackedArray(_, elty) => Some(UnpackedType::from_legacy(cx, elty).into()),
        TypeKind::BitScalar { .. } => Some(ty.into()),
        TypeKind::BitVector { .. } => Some(ty.into()),
        TypeKind::Struct(_) if repeat != 1 => {
            bug_span!(
                expr.span,
                cx,
                "struct patterns with repeat count other than 1 not supported",
            );
        }
        TypeKind::Struct(def_id) => {
            // TODO: This code shares quite some similarity with the one
            // in HIR lowering. It would be much smarter to create an
            // intermediate struct that distills patterns into proper
            // array/struct mappings, such that misalignments are
            // handled early on, and these type checks become easier.
            let def = match cx.struct_def(def_id.id()) {
                Ok(d) => d,
                Err(()) => return Some(UnpackedType::make_error().into()),
            };
            if args.len() > def.fields.len() {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "pattern has {} fields, but type `{}` requires {}",
                        args.len(),
                        ty,
                        def.fields.len()
                    ))
                    .span(expr.span),
                );
            }
            Some(
                cx.map_to_type(def.fields[index].ty, def_id.env())
                    .map(|ty| UnpackedType::from_legacy(cx, ty))
                    .unwrap_or(UnpackedType::make_error())
                    .into(),
            )
        }
        _ => {
            bug_span!(
                expr.span,
                cx,
                "type context for field {} of positional pattern with invalid type `{}`",
                ty,
                index
            );
        }
    }
}

/// Get the type context imposed by a statement.
///
/// Determine the type context `stmt` imposes on `onto`.
fn type_context_imposed_by_stmt<'gcx>(
    cx: &impl Context<'gcx>,
    onto: NodeId,
    stmt: &'gcx hir::Stmt,
    env: ParamEnv,
) -> Option<TypeContext2<'gcx>> {
    match stmt.kind {
        // Assignments impose the self-determined type of the other operand on
        // an operand, if available.
        hir::StmtKind::Assign { lhs, rhs, .. } => {
            if lhs == onto {
                cx.self_determined_type(rhs, env).map(Into::into)
            } else if rhs == onto {
                cx.self_determined_type(lhs, env).map(Into::into)
            } else {
                None
            }
        }

        // If statements and do/while loops require a boolean condition.
        hir::StmtKind::If { cond, .. } if onto == cond => Some(TypeContext2::Bool),

        // Do/while loops require a boolean condition.
        hir::StmtKind::Loop { kind, .. } => {
            match kind {
                hir::LoopKind::Repeat(count) if onto == count => {
                    // TODO: Actually this should require a simple 2-value bit vector type
                    None
                }
                hir::LoopKind::Do(cond)
                | hir::LoopKind::While(cond)
                | hir::LoopKind::For(_, cond, _)
                    if onto == cond =>
                {
                    Some(TypeContext2::Bool)
                }
                _ => None,
            }
        }

        // Case statements impose the switch expression's self-determined type
        // on  the case arms.
        hir::StmtKind::Case { expr, ref ways, .. } => {
            if ways.iter().flat_map(|(x, _)| x.iter()).any(|&x| x == onto) {
                cx.self_determined_type(expr, env).map(Into::into)
            } else {
                None
            }
        }

        _ => None,
    }
}

/// A type resulting from a sequence of casts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CastType<'a> {
    /// The initial type before casting.
    pub init: &'a ty::UnpackedType<'a>,
    /// The final type after casting.
    pub ty: &'a ty::UnpackedType<'a>,
    /// The cast operations that lead to the result.
    pub casts: Vec<(CastOp, &'a ty::UnpackedType<'a>)>,
}

/// A cast operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastOp {
    /// Pack a value into an SBVT.
    PackSBVT,
    /// Unpack a value from an SBVT.
    UnpackSBVT,
    /// Cast to a boolean.
    Bool,
    /// Cast to a different sign.
    Sign(ty::Sign),
    /// Cast to a different range. Second argument indicates sign-extension.
    Range(ty::Range, bool),
    /// Cast to a different domain.
    Domain(ty::Domain),
}

impl<'a> CastType<'a> {
    /// Check if this cast type is a tombstone.
    pub fn is_error(&self) -> bool {
        self.ty.is_error()
    }

    /// Add a cast operation.
    pub fn add_cast(&mut self, op: CastOp, ty: &'a ty::UnpackedType<'a>) {
        self.casts.push((op, ty));
        self.ty = ty;
    }
}

impl<'a> From<&'a ty::UnpackedType<'a>> for CastType<'a> {
    fn from(ty: &'a ty::UnpackedType<'a>) -> CastType<'a> {
        CastType {
            init: ty,
            ty,
            casts: vec![],
        }
    }
}

impl std::fmt::Display for CastType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.init)?;
        for (op, ty) in &self.casts {
            write!(f, " -> {:?} {}", op, ty)?;
        }
        Ok(())
    }
}

/// Check if an expression is in lvalue position.
pub(crate) fn expr_is_lvalue<'gcx>(cx: &impl Context<'gcx>, onto: NodeId, _env: ParamEnv) -> bool {
    let hir = match cx.hir_of(cx.parent_node_id(onto).unwrap()) {
        Ok(x) => x,
        Err(()) => return false,
    };
    match hir {
        HirNode::Expr(e) => match e.kind {
            hir::ExprKind::Unary(op, _) => match op {
                hir::UnaryOp::PreInc
                | hir::UnaryOp::PreDec
                | hir::UnaryOp::PostInc
                | hir::UnaryOp::PostDec => true,
                _ => false,
            },
            _ => false,
        },
        HirNode::Stmt(s) => match s.kind {
            hir::StmtKind::Assign { lhs, .. } => lhs == onto,
            _ => false,
        },
        HirNode::Assign(a) => a.lhs == onto,
        _ => false,
    }
}
