// Copyright (c) 2016-2020 Fabian Schuiki

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{bit_size_of_type, Domain, Sign, Type, TypeKind},
    value::ValueKind,
    ParamEnv, ParamEnvBinding,
};
use num::{cast::ToPrimitive, BigInt, One, Signed};

/// Determine the type of a node.
pub(crate) fn type_of<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Type<'gcx>> {
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
        HirNode::Expr(e) => Ok(type_of_expr(cx, e, env)),
        HirNode::ValueParam(p) => {
            if is_explicit_type(cx, p.ty)? {
                return cx.map_to_type(p.ty, env);
            }
            let env_data = cx.param_env_data(env);
            match env_data.find_value(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.type_of(assigned_id.0, assigned_id.1)
                }
                Some(ParamEnvBinding::Direct(t)) => return Ok(t.ty),
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
fn type_of_expr<'gcx>(cx: &impl Context<'gcx>, expr: &'gcx hir::Expr, env: ParamEnv) -> Type<'gcx> {
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
            .map(|x| x.ty())
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

        // Sign casts "forward" the type of their argument, with the sign
        // replaced.
        hir::ExprKind::Builtin(hir::BuiltinCall::Signed(arg)) => cx
            .type_of(arg, env)
            .unwrap_or(&ty::ERROR_TYPE)
            .change_sign(cx, Sign::Signed),
        hir::ExprKind::Builtin(hir::BuiltinCall::Unsigned(arg)) => cx
            .type_of(arg, env)
            .unwrap_or(&ty::ERROR_TYPE)
            .change_sign(cx, Sign::Unsigned),

        // Pattern expressions require a type context.
        hir::ExprKind::PositionalPattern(..)
        | hir::ExprKind::NamedPattern(..)
        | hir::ExprKind::RepeatPattern(..)
        | hir::ExprKind::EmptyPattern => cx.need_type_context(expr.id, env).ty(),

        // Function calls resolve to the function's return type.
        hir::ExprKind::FunctionCall(target, _) => cx
            .hir_of(target)
            .and_then(|hir| {
                let hir = match hir {
                    HirNode::Subroutine(s) => s,
                    _ => unreachable!(),
                };
                match hir.retty {
                    Some(retty_id) => cx.map_to_type(retty_id, env),
                    None => Ok(&ty::VOID_TYPE),
                }
            })
            .unwrap_or(&ty::ERROR_TYPE),
    }
}

/// Convert a node to a type.
pub(crate) fn map_to_type<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Type<'gcx>> {
    let hir = cx.hir_of(node_id)?;
    #[allow(unreachable_patterns)]
    match hir {
        HirNode::Type(hir) => map_type_kind(cx, node_id, env, hir, &hir.kind),
        HirNode::TypeParam(param) => {
            let env_data = cx.param_env_data(env);
            match env_data.find_type(node_id) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.map_to_type(assigned_id.0, assigned_id.1)
                }
                Some(ParamEnvBinding::Direct(t)) => return Ok(t),
                _ => (),
            }
            if let Some(default) = param.default {
                return cx.map_to_type(default, env);
            }
            let mut d = DiagBuilder2::error(format!(
                "{} not assigned and has no default",
                param.desc_full(),
            ));
            let contexts = cx.param_env_contexts(env);
            for &context in &contexts {
                d = d.span(cx.span(context));
            }
            if contexts.is_empty() {
                d = d.span(param.human_span());
            }
            cx.emit(d);
            Err(())
        }
        HirNode::Typedef(def) => cx.map_to_type(def.ty, env),

        // Certain expressions are actually types. In that case we also support
        // a mapping to a type.
        HirNode::Expr(hir) => match hir.kind {
            hir::ExprKind::Ident(name) => {
                let binding = cx.resolve_upwards_or_error(name, node_id)?;
                Ok(cx.mkty_named(name, (binding, env)))
            }
            hir::ExprKind::Scope(scope_id, name) => {
                let within = cx.resolve_node(scope_id, env)?;
                let binding = cx.resolve_downwards_or_error(name, within)?;
                Ok(cx.mkty_named(name, (binding, env)))
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
        hir::TypeKind::Builtin(hir::BuiltinType::Time) => Ok(&ty::LONGINT_TYPE), // TODO(fschuiki): Fix this
        hir::TypeKind::Builtin(hir::BuiltinType::String) => {
            Ok(cx.mkty_packed_array(1, &ty::BYTE_TYPE))
        }
        hir::TypeKind::Named(name) => {
            let binding = cx.resolve_upwards_or_error(name, node_id)?;
            Ok(cx.mkty_named(name, (binding, env)))
        }
        hir::TypeKind::Scope(scope_id, name) => {
            let within = cx.resolve_node(scope_id, env)?;
            let binding = cx.resolve_downwards_or_error(name, within)?;
            Ok(cx.mkty_named(name, (binding, env)))
        }
        hir::TypeKind::Struct(..) => Ok(cx.mkty_struct(node_id)),
        hir::TypeKind::PackedArray(ref inner, lhs, rhs) => {
            let map_bound = |bound: NodeId| -> Result<&num::BigInt> {
                match cx.constant_value_of(bound, env)?.kind {
                    ValueKind::Int(ref int, ..) => Ok(int),
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

/// Get the self-determined type of a node.
pub(crate) fn self_determined_type<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Option<Type<'gcx>> {
    let hir = match cx.hir_of(node_id) {
        Ok(x) => x,
        Err(()) => return Some(&ty::ERROR_TYPE),
    };
    match hir {
        HirNode::Expr(e) => self_determined_expr_type(cx, e, env),
        _ => None,
    }
}

/// Require a node to have a self-determined type.
///
/// Emits an error if the node has no self-determined type.
pub(crate) fn need_self_determined_type<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Type<'gcx> {
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
                        "The type of {} must be inferred from \
                         context, but the location where you used it does not \
                         provide such information.",
                        desc
                    ))
                    .add_note(format!("Try a cast: `T'({})`", extract)),
            );
            &ty::ERROR_TYPE
        }
    }
}

/// Get the self-determined type of an expression.
fn self_determined_expr_type<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &'gcx hir::Expr,
    env: ParamEnv,
) -> Option<Type<'gcx>> {
    match expr.kind {
        // Unsized constants fall back to their single bit equivalent.
        hir::ExprKind::UnsizedConst(_) => Some(&ty::LOGIC_TYPE),

        // Sized integer constants have a well-defined type.
        // TODO(fschuiki): Inherit signedness from `s` character in base.
        hir::ExprKind::IntConst { width, signed, .. } => {
            Some(cx.intern_type(TypeKind::BitVector {
                domain: ty::Domain::TwoValued, // TODO(fschuiki): Is this correct?
                sign: if signed {
                    ty::Sign::Signed
                } else {
                    ty::Sign::Unsigned
                },
                range: ty::Range {
                    size: width,
                    dir: ty::RangeDir::Down,
                    offset: 0isize,
                },
                dubbed: true,
            }))
        }

        // Time constants are of time type.
        hir::ExprKind::TimeConst(_) => Some(cx.mkty_time()),

        // String literals are of string type.
        hir::ExprKind::StringConst(_) => Some(cx.mkty_packed_array(1, &ty::BYTE_TYPE)),

        // Identifiers and scoped identifiers inherit their type from the bound
        // node.
        hir::ExprKind::Ident(_) | hir::ExprKind::Scope(..) => Some(
            cx.resolve_node(expr.id, env)
                .and_then(|x| cx.type_of(x, env))
                .unwrap_or(&ty::ERROR_TYPE),
        ),

        // Concatenation yields an unsigned logic vector whose bit width is the
        // sum of the simple bit vector types of each argument.
        //
        // See "11.8.1 Rules for expression types".
        hir::ExprKind::Concat(repeat, ref exprs) => {
            let mut failed = false;

            // Determine the cumulative width of all fields.
            // TODO(fschuiki): Use a more benign function that does not fail,
            // but returns an option which can be used to hint the user at the
            // fact that the concatenation only accepts packable types.
            let mut bit_width = 0;
            for &expr in exprs {
                match cx
                    .type_of(expr, env)
                    .and_then(|ty| bit_size_of_type(cx, ty, env))
                {
                    Ok(w) => bit_width += w,
                    Err(()) => failed = true,
                }
            }

            // Determine the repetition factor.
            let repeat = match repeat.map(|r| cx.constant_int_value_of(r, env)) {
                Some(Ok(r)) => r.to_usize().unwrap(),
                Some(Err(_)) => {
                    failed = true;
                    0
                }
                None => 1,
            };

            // Package up the result.
            Some(if failed {
                &ty::ERROR_TYPE
            } else {
                cx.intern_type(TypeKind::BitVector {
                    sign: Sign::Unsigned,
                    domain: Domain::FourValued,
                    range: ty::Range {
                        size: repeat * bit_width,
                        dir: ty::RangeDir::Down,
                        offset: 0isize,
                    },
                    dubbed: false,
                })
            })
        }

        // Casts trivially evaluate to the cast type.
        hir::ExprKind::Cast(ty, _) => Some(cx.map_to_type(ty, env).unwrap_or(&ty::ERROR_TYPE)),

        // Sign casts trivially evaluate to the sign-converted inner type.
        hir::ExprKind::CastSign(sign, arg) => cx
            .self_determined_type(arg, env)
            .map(|x| x.change_sign(cx, sign.value)),

        // Sign casts trivially evaluate to the size-converted inner type.
        hir::ExprKind::CastSize(size, arg) => {
            let mut failed = false;

            // Determine the actual size.
            let size = match cx.constant_int_value_of(size, env) {
                Ok(r) => r.to_usize().unwrap(),
                Err(_) => {
                    failed = true;
                    0
                }
            };

            // Map the inner type to a simple bit vector.
            let inner_ty = cx.need_self_determined_type(arg, env);
            failed |= inner_ty.is_error();

            // Create a new type with the correct size.
            Some(if failed {
                &ty::ERROR_TYPE
            } else {
                cx.intern_type(TypeKind::BitVector {
                    domain: inner_ty.get_value_domain().unwrap_or(Domain::TwoValued),
                    sign: inner_ty.get_sign().unwrap_or(Sign::Unsigned),
                    range: ty::Range {
                        size: size,
                        dir: ty::RangeDir::Down,
                        offset: 0isize,
                    },
                    dubbed: false,
                })
            })
        }

        // The `inside` expression evaluates to a boolean.
        hir::ExprKind::Inside(..) => Some(&ty::LOGIC_TYPE),

        // Most builtin functions evaluate to the integer type.
        hir::ExprKind::Builtin(hir::BuiltinCall::Unsupported)
        | hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(_))
        | hir::ExprKind::Builtin(hir::BuiltinCall::Bits(_)) => Some(&ty::INT_TYPE),

        // Sign casts reflect their argument, but with the sign changed.
        hir::ExprKind::Builtin(hir::BuiltinCall::Signed(arg)) => cx
            .self_determined_type(arg, env)
            .map(|x| x.change_sign(cx, Sign::Signed)),
        hir::ExprKind::Builtin(hir::BuiltinCall::Unsigned(arg)) => cx
            .self_determined_type(arg, env)
            .map(|x| x.change_sign(cx, Sign::Unsigned)),

        // Member field accesses resolve to the type of the member.
        hir::ExprKind::Field(..) => Some(
            cx.resolve_field_access(expr.id, env)
                .and_then(|(_, _, field_id)| cx.type_of(field_id, env))
                .unwrap_or(&ty::ERROR_TYPE),
        ),

        // Bit- and part-select expressions
        hir::ExprKind::Index(target, mode) => Some({
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
                Err(_) => return Some(&ty::ERROR_TYPE),
            };

            // TODO(fschuiki): In case the target type is not something we can
            // directly index into, map it to the equivalent simple bit vector
            // type first.
            let target_ty = cx.type_of(target, env).unwrap_or(&ty::ERROR_TYPE);
            match *target_ty.unname() {
                TypeKind::PackedArray(_, ty) => {
                    if let Some(width) = width {
                        cx.intern_type(TypeKind::PackedArray(width, ty))
                    } else {
                        ty
                    }
                }
                TypeKind::Bit(domain) | TypeKind::Int(_, domain) => {
                    cx.intern_type(TypeKind::BitVector {
                        domain,
                        sign: Sign::Signed,
                        range: ty::Range {
                            size: width.unwrap_or(1),
                            dir: ty::RangeDir::Down,
                            offset: 0isize,
                        },
                        dubbed: false,
                    })
                }
                TypeKind::BitScalar { domain, sign } => cx.intern_type(TypeKind::BitVector {
                    domain,
                    sign,
                    range: ty::Range {
                        size: width.unwrap_or(1),
                        dir: ty::RangeDir::Down,
                        offset: 0isize,
                    },
                    dubbed: false,
                }),
                TypeKind::BitVector {
                    domain,
                    sign,
                    range,
                    ..
                } => cx.intern_type(TypeKind::BitVector {
                    domain,
                    sign,
                    range: ty::Range {
                        size: width.unwrap_or(1),
                        dir: range.dir,
                        offset: 0isize,
                    },
                    dubbed: false,
                }),
                TypeKind::Error => (target_ty),
                _ => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "cannot index into a value of type `{}`",
                            target_ty
                        ))
                        .span(expr.span()),
                    );
                    error!("Type is {:?}", target_ty);
                    &ty::ERROR_TYPE
                }
            }
        }),

        // Some unary operators have a fully self-determined type.
        hir::ExprKind::Unary(op, arg) => match op {
            // Handle the self-determined cases.
            hir::UnaryOp::LogicNot
            | hir::UnaryOp::RedAnd
            | hir::UnaryOp::RedOr
            | hir::UnaryOp::RedXor
            | hir::UnaryOp::RedNand
            | hir::UnaryOp::RedNor
            | hir::UnaryOp::RedXnor => Some(&ty::LOGIC_TYPE),

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
            | hir::BinaryOp::LogicOr => Some(&ty::LOGIC_TYPE),

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

        _ => None,
    }
}

/// Get the operation type of an expression.
pub(crate) fn operation_type<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Option<Type<'gcx>> {
    let hir = match cx.hir_of(node_id) {
        Ok(x) => x,
        Err(_) => return Some(&ty::ERROR_TYPE),
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
                hir::UnaryOp::LogicNot => Some(&ty::LOGIC_TYPE),
            };
            if ty.is_none() {
                cx.emit(
                    DiagBuilder2::error(format!("type of {} cannot be inferred", expr.desc_full()))
                        .span(expr.human_span())
                        .add_note(
                            "The operand does not have a self-determined type, \
                             and the type cannot be inferred from the context.",
                        )
                        .add_note(format!("Try a cast: `T'({})`", expr.span().extract())),
                );
                Some(&ty::ERROR_TYPE)
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
                hir::BinaryOp::LogicAnd | hir::BinaryOp::LogicOr => Some(&ty::LOGIC_TYPE),

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
                            "Neither of the operands has a self-determined type, \
                             and the type cannot be inferred from the context.",
                        )
                        .add_note(format!("Try a cast: `T'({})`", expr.span().extract())),
                );
                Some(&ty::ERROR_TYPE)
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

        _ => None,
    }
}

/// Determine the bit length, sign, and value domain of the types that influence
/// an expression.
fn unify_operator_types<'gcx>(
    cx: &impl Context<'gcx>,
    env: ParamEnv,
    types: impl Iterator<Item = Type<'gcx>>,
) -> Option<Type<'gcx>> {
    // Map the iterator to a sequence of sign, domain, and bit width tuples.
    let inner: Vec<_> = types
        .flat_map(|ty| {
            bit_size_of_type(cx, ty, env).map(|w| ((ty.get_sign(), ty.get_value_domain(), w)))
        })
        .collect();

    // Determine the maximum width, sign, and domain.
    let width: Option<usize> = inner.iter().map(|&(_, _, w)| w).max();
    let sign = match inner.iter().all(|&(s, _, _)| s == Some(Sign::Signed)) {
        true => Sign::Signed,
        false => Sign::Unsigned,
    };
    let domain = match inner.iter().all(|&(_, d, _)| d == Some(Domain::TwoValued)) {
        true => Domain::TwoValued,
        false => Domain::FourValued,
    };

    // Construct the type.
    width.map(|w| {
        cx.intern_type(TypeKind::BitVector {
            sign,
            domain,
            range: ty::Range {
                size: w,
                dir: ty::RangeDir::Down,
                offset: 0isize,
            },
            dubbed: false,
        })
    })
}

/// Require a node to have an operation type.
///
/// Emits an error if the node has no operation type.
pub(crate) fn need_operation_type<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Type<'gcx> {
    match cx.operation_type(node_id, env) {
        Some(x) => x,
        None => {
            let span = cx.span(node_id);
            cx.emit(
                DiagBuilder2::bug(format!("`{}` has no operation type", span.extract())).span(span),
            );
            &ty::ERROR_TYPE
        }
    }
}

/// Get the type context of a node.
pub(crate) fn type_context<'gcx>(
    cx: &impl Context<'gcx>,
    onto: NodeId,
    env: ParamEnv,
) -> Option<TypeContext<'gcx>> {
    let hir = match cx.hir_of(cx.parent_node_id(onto).unwrap()) {
        Ok(x) => x,
        Err(()) => return None,
    };
    match hir {
        HirNode::Expr(e) => type_context_imposed_by_expr(cx, onto, e, env),
        HirNode::Assign(a) => {
            if a.lhs == onto {
                cx.self_determined_type(a.rhs, env).map(Into::into)
            } else if a.rhs == onto {
                cx.self_determined_type(a.lhs, env).map(Into::into)
            } else {
                None
            }
        }
        // TODO(fschuiki): Ports
        HirNode::VarDecl(v)
            if v.init == Some(onto) && is_explicit_type(cx, v.ty).unwrap_or(false) =>
        {
            Some(cx.map_to_type(v.ty, env).unwrap_or(&ty::ERROR_TYPE).into())
        }
        HirNode::ValueParam(v)
            if v.default == Some(onto) && is_explicit_type(cx, v.ty).unwrap_or(false) =>
        {
            Some(cx.map_to_type(v.ty, env).unwrap_or(&ty::ERROR_TYPE).into())
        }
        // TODO(fschuiki): Statements
        _ => None,
    }
}

/// Get the type context of a node.
pub(crate) fn need_type_context<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> TypeContext<'gcx> {
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
                        "The type of {} must be inferred from \
                         context, but the location where you used it does not \
                         provide such information.",
                        desc
                    ))
                    .add_note(format!("Try a cast: `T'({})`", extract)),
            );
            TypeContext::Type(&ty::ERROR_TYPE)
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
    /// This resolves implicit boolean casts to the `bit` type.
    pub fn ty(&self) -> Type<'a> {
        match *self {
            TypeContext::Type(t) => t,
            TypeContext::Bool => &ty::BIT_TYPE,
        }
    }
}

impl<'a> From<Type<'a>> for TypeContext<'a> {
    fn from(ty: Type<'a>) -> Self {
        TypeContext::Type(ty)
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
) -> Option<TypeContext<'gcx>> {
    match expr.kind {
        hir::ExprKind::Unary(op, _) => match op {
            // The unary operators whose output type does not depend on the
            // operands also do not impose a type context on their operands.
            hir::UnaryOp::LogicNot
            | hir::UnaryOp::RedAnd
            | hir::UnaryOp::RedOr
            | hir::UnaryOp::RedXor
            | hir::UnaryOp::RedNand
            | hir::UnaryOp::RedNor
            | hir::UnaryOp::RedXnor => None,

            // For all other cases we impose our self-determined type as
            // context.
            hir::UnaryOp::Neg
            | hir::UnaryOp::Pos
            | hir::UnaryOp::BitNot
            | hir::UnaryOp::PreInc
            | hir::UnaryOp::PreDec
            | hir::UnaryOp::PostInc
            | hir::UnaryOp::PostDec => cx.self_determined_type(expr.id, env).map(Into::into),
        },

        hir::ExprKind::Binary(op, lhs, _) => match op {
            // The binary operators whose output type does not depend on the
            // operands also do not impose a type context on their operands.
            hir::BinaryOp::Eq
            | hir::BinaryOp::Neq
            | hir::BinaryOp::Lt
            | hir::BinaryOp::Leq
            | hir::BinaryOp::Gt
            | hir::BinaryOp::Geq
            | hir::BinaryOp::LogicAnd
            | hir::BinaryOp::LogicOr => None,

            // Exponentiation and shifts impose a type context on their left
            // hand side.
            hir::BinaryOp::Pow
            | hir::BinaryOp::LogicShL
            | hir::BinaryOp::LogicShR
            | hir::BinaryOp::ArithShL
            | hir::BinaryOp::ArithShR => {
                if onto == lhs {
                    cx.self_determined_type(expr.id, env).map(Into::into)
                } else {
                    None
                }
            }

            // For all other cases we impose our self-determined type as
            // context.
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
            | hir::BinaryOp::BitXnor => cx.self_determined_type(expr.id, env).map(Into::into),
        },

        // The ternary operator imposes its self-determined type as a context.
        hir::ExprKind::Ternary(_, lhs, rhs) if onto == lhs || onto == rhs => {
            cx.self_determined_type(expr.id, env).map(Into::into)
        }

        // Sign casts forward their type context to the argument..
        hir::ExprKind::Builtin(hir::BuiltinCall::Signed(_))
        | hir::ExprKind::Builtin(hir::BuiltinCall::Unsigned(_)) => {
            cx.self_determined_type(expr.id, env).map(Into::into)
        }

        _ => None,
    }
}
