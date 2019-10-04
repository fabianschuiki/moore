// Copyright (c) 2016-2019 Fabian Schuiki

use crate::{
    crate_prelude::*,
    hir::HirNode,
    ty::{bit_size_of_type, Type, TypeKind},
    value::ValueKind,
    ParamEnv, ParamEnvBinding,
};
use num::{cast::ToPrimitive, One};

/// Determine the type of a node.
pub(crate) fn type_of<'gcx>(
    cx: &impl Context<'gcx>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<Type<'gcx>> {
    let hir = cx.hir_of(node_id)?;
    #[allow(unreachable_patterns)]
    match hir {
        HirNode::Port(p) => cx.map_to_type(p.ty, env),
        HirNode::Expr(e) => match e.kind {
            hir::ExprKind::IntConst(width, _) => Ok(cx.mkty_int(width)),
            hir::ExprKind::UnsizedConst(_) => Ok(cx.mkty_int(1)),
            hir::ExprKind::TimeConst(_) => Ok(cx.mkty_time()),
            hir::ExprKind::Ident(_) => cx.type_of(cx.resolve_node(node_id, env)?, env),
            hir::ExprKind::Unary(op, arg) => {
                let arg_ty = cx.type_of(arg, env)?;
                Ok(match op {
                    hir::UnaryOp::Neg
                    | hir::UnaryOp::BitNot
                    | hir::UnaryOp::PreInc
                    | hir::UnaryOp::PreDec
                    | hir::UnaryOp::PostInc
                    | hir::UnaryOp::PostDec => arg_ty,
                    hir::UnaryOp::LogicNot => cx.mkty_bit(),
                    _ => {
                        error!("{:#?}", hir);
                        return cx.unimp_msg("type analysis of", &hir);
                    }
                })
            }
            hir::ExprKind::Binary(op, lhs, rhs) => {
                let lhs_ty = cx.type_of(lhs, env)?;
                let _rhs_ty = cx.type_of(rhs, env)?;
                // TODO(fschuiki): Actually use lhs and rhs, and query the type
                // context (optional) from the parent node, to determine the
                // width of the result (max over all bit widths). This requires
                // mapping the types to the equivalent simple bit vector type.
                Ok(match op {
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
                    | hir::BinaryOp::BitXnor => lhs_ty,
                    hir::BinaryOp::Eq
                    | hir::BinaryOp::Neq
                    | hir::BinaryOp::Lt
                    | hir::BinaryOp::Leq
                    | hir::BinaryOp::Gt
                    | hir::BinaryOp::Geq
                    | hir::BinaryOp::LogicAnd
                    | hir::BinaryOp::LogicOr => cx.mkty_bit(),
                    _ => {
                        error!("{:#?}", hir);
                        return cx.unimp_msg("type analysis of", &hir);
                    }
                })
            }
            hir::ExprKind::Field(..) => {
                let (_, _, field_id) = cx.resolve_field_access(node_id, env)?;
                cx.type_of(field_id, env)
            }
            hir::ExprKind::Index(target, mode) => {
                let target_ty = cx.type_of(target, env)?;
                match mode {
                    hir::IndexMode::One(..) => match *target_ty {
                        TypeKind::PackedArray(_, ty) => Ok(ty),
                        TypeKind::Int(_, ty::Domain::TwoValued) => Ok(cx.mkty_bit()),
                        TypeKind::Int(_, ty::Domain::FourValued) => Ok(cx.mkty_logic()),
                        _ => {
                            let hir = cx.hir_of(target)?;
                            cx.emit(
                                DiagBuilder2::error(format!(
                                    "{} cannot be indexed into",
                                    hir.desc_full()
                                ))
                                .span(hir.human_span()),
                            );
                            Err(())
                        }
                    },
                    hir::IndexMode::Many(..) => Ok(target_ty),
                }
            }
            hir::ExprKind::Builtin(hir::BuiltinCall::Clog2(_))
            | hir::ExprKind::Builtin(hir::BuiltinCall::Bits(_)) => Ok(cx.mkty_int(32)),
            hir::ExprKind::Builtin(hir::BuiltinCall::Signed(arg))
            | hir::ExprKind::Builtin(hir::BuiltinCall::Unsigned(arg)) => cx.type_of(arg, env),
            hir::ExprKind::Ternary(_cond, true_expr, _false_expr) => cx.type_of(true_expr, env),
            hir::ExprKind::Scope(..) => cx.type_of(cx.resolve_node(node_id, env)?, env),
            hir::ExprKind::PositionalPattern(..)
            | hir::ExprKind::NamedPattern(..)
            | hir::ExprKind::RepeatPattern(..)
            | hir::ExprKind::EmptyPattern => cx.type_of(cx.parent_node_id(node_id).unwrap(), env),
            hir::ExprKind::Concat(repeat, ref exprs) => {
                let mut bit_width = 0;
                for &expr in exprs {
                    let ty = cx.type_of(expr, env)?;
                    bit_width += bit_size_of_type(cx, ty, env)?;
                }
                let repeat = match repeat {
                    Some(repeat) => cx.constant_int_value_of(repeat, env)?.to_usize().unwrap(),
                    None => 1,
                };
                Ok(cx.mkty_int(repeat * bit_width))
            }
            hir::ExprKind::Cast(ty, _) => cx.map_to_type(ty, env),
            _ => {
                error!("{:#?}", hir);
                cx.unimp_msg("type analysis of", &hir)
            }
        },
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
        HirNode::GenvarDecl(_) => Ok(cx.mkty_int(32)),
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
        HirNode::Package(_) => Ok(cx.mkty_void()),
        HirNode::Assign(a) => cx.type_of(a.lhs, env),
        _ => {
            error!("{:#?}", hir);
            cx.unimp_msg("type analysis of", &hir)
        }
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
                    ValueKind::Int(ref int) => Ok(int),
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
                hir::TypeKind::Builtin(hir::BuiltinType::Bit) => {
                    Ok(cx.intern_type(TypeKind::BitVector {
                        domain: ty::Domain::TwoValued,
                        sign: ty::Sign::Unsigned,
                        range: ty::Range { size, dir, offset },
                        dubbed: false,
                    }))
                }
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
        hir::TypeKind::Implicit => unreachable!("implicit type not resolved"),
        _ => {
            error!("{:#?}", root);
            cx.unimp_msg("type analysis of", root)
        }
    }
}
