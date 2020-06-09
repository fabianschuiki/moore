// Copyright (c) 2016-2020 Fabian Schuiki

//! Type checking and computation.
//!
//! This module performs type computation and type checking of a SystemVerilog
//! design. A large portion is dedicated to expression typing, which is the most
//! involved angle. However, there are also other bits and pieces that compute
//! types for things like ports or instances. Finally, there are functions that
//! map AST nodes of type kind to actual `UnpackedType`s.
//!
//! Expression type checking occurs in the following sequence, and through the
//! following queries:
//!
//! 1. `self_determined_type` evaluates an expression to its self-determined
//!    type, or returns `None` if the expression requires context information to
//!    determine a type. There is also `need_self_determined_type` which issues
//!    a diagnostic in the latter case.
//! 2. `operation_type` determines if an expression has an internal type under
//!    which its operation takes place. E.g. comparisons have the expanded arg.
//!    types as operation type. There is also `need_operation_type`.
//! 3. `type_context` determines what type the parent of an expression imposes
//!    on the expression. In an assignment for example, this would be the left
//!    hand side's type impose on the right hand side, and vice versa. This is
//!    the main driver for casting operations, and the rest of the compiler
//!    expects the type context to fully line up with the parent's needs.
//! 4. `type_of_expr` computes the type of an expression *before casting*.
//! 5. `cast_type` computes the final type of an expression, ensuring that its
//!    type as returned by `type_of_expr` is castable, and deriving a cast
//!    sequence` to the `type_context`.

use crate::crate_prelude::*;
use crate::{
    common::arenas::Alloc,
    hir::HirNode,
    port_list,
    resolver::{DefNode, InstTarget},
    ty::{
        Domain, IntAtomType, IntVecType, PackedCore, PackedType, RealType, SbvType, Sign,
        UnpackedCore, UnpackedType,
    },
    value::ValueKind,
    ParamEnv, ParamEnvBinding,
};
use num::{cast::ToPrimitive, BigInt, One, Signed};
use std::collections::HashSet;

/// Determine the type of a node.
#[moore_derive::query]
pub(crate) fn type_of<'a>(
    cx: &impl Context<'a>,
    node_id: NodeId,
    env: ParamEnv,
) -> Result<&'a UnpackedType<'a>> {
    // Handle the cases we can already do on the AST.
    let ast = cx.ast_for_id(node_id);
    match ast.as_all() {
        ast::AllNode::VarDeclName(name) => match name.get_parent().unwrap().as_all() {
            ast::AllNode::VarDecl(..) => return Ok(cx.type_of_var_decl(Ref(name), env)),
            ast::AllNode::NetDecl(..) => return Ok(cx.type_of_net_decl(Ref(name), env)),
            ast::AllNode::StructMember(..) => return Ok(cx.type_of_struct_member(Ref(name), env)),
            x => bug_span!(ast.span(), cx, "VarDeclName with weird parent {:?}", x),
        },
        ast::AllNode::ParamValueDecl(x) => return Ok(cx.type_of_value_param(Ref(x), env)),
        _ => (),
    };

    // Handle all the other cases.
    let hir = cx.hir_of(node_id)?;
    #[allow(unreachable_patterns)]
    match hir {
        HirNode::IntPort(p) => Ok(cx.type_of_int_port(Ref(p), env)),
        HirNode::ExtPort(p) => Ok(cx.type_of_ext_port(Ref(p), env)),
        HirNode::Expr(_) => Ok(cx.cast_type(node_id, env).unwrap().ty),
        HirNode::GenvarDecl(_) => {
            Ok(SbvType::nice(ty::Domain::TwoValued, ty::Sign::Signed, 32).to_unpacked(cx))
        }
        HirNode::EnumVariant(v) => {
            let ty = cx.packed_type_from_ast(
                Ref(cx
                    .ast_for_id(v.enum_id)
                    .as_all()
                    .get_type()
                    .expect("enum_id should resolve to a type")),
                env,
                None,
            );
            if ty.is_error() {
                return Ok(ty);
            }
            let packed = match ty.resolve_full().core {
                ty::UnpackedCore::Packed(p) => p,
                _ => panic!("enum type should have a packed core; got `{}`", ty),
            };
            let enm = match packed.resolve_full().core {
                ty::PackedCore::Enum(ref e) => e,
                _ => panic!("enum type should actually be an enum; got `{}`", packed),
            };
            Ok(enm.base.to_unpacked(cx))
        }
        HirNode::Package(_) => Ok(UnpackedType::make_void()),
        HirNode::Assign(_) => unreachable!("has no type: {:?}", hir),
        HirNode::Inst(hir) => Ok(cx.type_of_inst(Ref(hir), env)),
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

/// Determine the type of an internal port.
#[moore_derive::query]
pub(crate) fn type_of_int_port<'a>(
    cx: &impl Context<'a>,
    Ref(port): Ref<'a, port_list::IntPort<'a>>,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    match port.data {
        Some(ref data) => cx.packed_type_from_ast(Ref(data.ty), env, None),
        None => {
            // Resolve the port to a net/var decl in the module, then use
            // that decl's type.
            cx.resolve_node(port.id, env)
                .and_then(|decl_id| cx.type_of(decl_id, env))
                .unwrap_or(UnpackedType::make_error())
        }
    }
}

/// Determine the type of an external port.
#[moore_derive::query]
pub(crate) fn type_of_ext_port<'a>(
    cx: &impl Context<'a>,
    Ref(port): Ref<'a, port_list::ExtPort<'a>>,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    if port.exprs.len() == 1 {
        let expr = &port.exprs[0];
        if !expr.selects.is_empty() {
            bug_span!(
                port.span,
                cx,
                "port{} contains a `[...]` selection; not yet supported in typeck",
                port.name
                    .map(|n| format!(" `{}`", n))
                    .unwrap_or_else(String::new)
            );
        }
        let port_list = cx.canonicalize_ports(port.node);
        cx.type_of_int_port(Ref(&port_list.int[expr.port]), env)
    } else {
        bug_span!(
            port.span,
            cx,
            "port{} is a concatenation; not yet supported in typeck",
            port.name
                .map(|n| format!(" `{}`", n))
                .unwrap_or_else(String::new)
        );
    }
}

/// Determine the type of a variable declaration.
#[moore_derive::query]
pub(crate) fn type_of_var_decl<'a>(
    cx: &impl Context<'a>,
    Ref(ast): Ref<'a, ast::VarDeclName<'a>>,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    let ast_decl = ast
        .get_parent()
        .unwrap()
        .as_all()
        .get_var_decl()
        .expect("parent not a VarDecl");
    type_of_varlike(cx, ast_decl, &ast_decl.ty, ast, &ast.dims, env)
}

/// Determine the type of a net declaration.
#[moore_derive::query]
pub(crate) fn type_of_net_decl<'a>(
    cx: &impl Context<'a>,
    Ref(ast): Ref<'a, ast::VarDeclName<'a>>,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    let ast_decl = ast
        .get_parent()
        .unwrap()
        .as_all()
        .get_net_decl()
        .expect("parent not a NetDecl");
    type_of_varlike(cx, ast_decl, &ast_decl.ty, ast, &ast.dims, env)
}

/// Determine the type of a struct member.
#[moore_derive::query]
pub(crate) fn type_of_struct_member<'a>(
    cx: &impl Context<'a>,
    Ref(ast): Ref<'a, ast::VarDeclName<'a>>,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    let ast_member = ast
        .get_parent()
        .unwrap()
        .as_all()
        .get_struct_member()
        .expect("parent not a StructMember");
    type_of_varlike(cx, ast_member, &ast_member.ty, ast, &ast.dims, env)
}

/// Determine the type of something variable-like. This includes variable and
/// net declarations, as well as struct fields.
fn type_of_varlike<'a>(
    cx: &impl Context<'a>,
    ast_decl: &'a dyn ast::AnyNode<'a>,
    ast_ty: &'a ast::Type<'a>,
    ast_name: &'a ast::VarDeclName<'a>,
    ast_dims: &'a [ast::TypeDim<'a>],
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    // If this is a net declaration, we map implicit types to the default net
    // type.
    let ast_implicit_default = if ast_decl.as_all().is_net_decl() {
        Some(ty::PackedCore::IntVec(ty::IntVecType::Logic))
    } else {
        None
    };

    // Handle the trivial case where the type is explicit.
    if !ast_ty.is_implicit() || ast_implicit_default.is_some() {
        return cx.unpacked_type_from_ast(Ref(ast_ty), Ref(ast_dims), env, ast_implicit_default);
    }

    // Handle the case where the type is implicit, but we can infer it from the
    // initial value.
    if let Some(init) = &ast_name.init {
        let hir = match cx.hir_of(init.id()) {
            Ok(HirNode::Expr(e)) => e,
            Err(()) => return UnpackedType::make_error(),
            _ => unreachable!(),
        };
        return cx.type_of_expr(Ref(hir), env);
    }

    // Otherwise complain.
    cx.emit(
        DiagBuilder2::error(format!(
            "`{}` has implicit type but is not initialized",
            ast_name.name
        ))
        .span(ast_name.name_span)
        .add_note("specify a type or add an initial value"),
    );
    UnpackedType::make_error()
}

/// Determine the type of a value parameter.
#[moore_derive::query]
pub(crate) fn type_of_value_param<'a>(
    cx: &impl Context<'a>,
    Ref(ast): Ref<'a, ast::ParamValueDecl<'a>>,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    // Handle the trivial case where the type is explicit.
    if !ast.ty.is_implicit() {
        return cx.unpacked_type_from_ast(Ref(&ast.ty), Ref(&ast.dims), env, None);
    }

    // Otherwise see what the parameter is bound to, an use that for the type.
    let env_data = cx.param_env_data(env);
    match env_data.find_value(ast.id()) {
        Some(ParamEnvBinding::Indirect(assigned_id)) => {
            let hir = match cx.hir_of(assigned_id.id()) {
                Ok(HirNode::Expr(e)) => e,
                Err(()) => return UnpackedType::make_error(),
                _ => unreachable!(),
            };
            return cx.type_of_expr(Ref(hir), assigned_id.env());
        }
        Some(ParamEnvBinding::Direct(t)) => return t.ty,
        _ => (),
    }

    // Otherwise try to infer the type from the default expression.
    if let Some(ref expr) = ast.expr {
        let hir = match cx.hir_of(expr.id()) {
            Ok(HirNode::Expr(e)) => e,
            Err(()) => return UnpackedType::make_error(),
            _ => unreachable!(),
        };
        return cx.type_of_expr(Ref(hir), env);
    }

    // Otherwise complain.
    cx.emit(
        DiagBuilder2::error(format!(
            "{} has implicit type but was not assigned and has no default",
            ast
        ))
        .span(ast.human_span())
        .add_note("specify a type for the parameter; or")
        .add_note("add a default value for the parameter; or")
        .add_note("override the parameter from outside"),
    );
    UnpackedType::make_error()
}

/// Determine the type of an instance.
#[moore_derive::query]
pub(crate) fn type_of_inst<'a>(
    cx: &impl Context<'a>,
    Ref(hir): Ref<'a, hir::Inst<'a>>,
    env: ParamEnv,
) -> &'a UnpackedType<'a> {
    let details = match cx.inst_details(Ref(hir), env) {
        Ok(x) => x,
        _ => return UnpackedType::make_error(),
    };
    UnpackedType::make(
        cx,
        match details.target.kind {
            InstTarget::Module(ast) => ty::UnpackedCore::Module {
                ast,
                env: details.inner_env,
            },
            InstTarget::Interface(ast) => ty::UnpackedCore::Interface {
                ast,
                env: details.inner_env,
            },
        },
    )
}

/// Map an AST node to the type it represents.
///
/// Returns `None` if the given AST node does not evaluate to a type.
#[moore_derive::query]
pub(crate) fn map_to_type<'a>(
    cx: &impl Context<'a>,
    Ref(ast): Ref<'a, dyn ast::AnyNode<'a>>,
    env: ParamEnv,
) -> Option<&'a UnpackedType<'a>> {
    match ast.as_all() {
        ast::AllNode::Type(ast) => Some(cx.packed_type_from_ast(Ref(ast), env, None)),
        ast::AllNode::Interface(ast) => {
            Some(UnpackedType::make(cx, UnpackedCore::Interface { ast, env }))
        }
        // The following is an ugly hack, and should actually never happen. But
        // as the HIR is implemented at the moment, certain parameter bindings
        // can bind expressions to type parameters.
        ast::AllNode::Expr(ast) => {
            let ast = cx.arena().alloc(ast::TypeOrExpr::Expr(ast));
            debug!("Disambiguating {:?}", ast);
            let rst = match cx.disamb_type_or_expr(Ref(ast)) {
                Ok(rst) => rst,
                Err(()) => return Some(UnpackedType::make_error()),
            };
            match rst {
                ast::TypeOrExpr::Type(ast) => Some(cx.packed_type_from_ast(Ref(ast), env, None)),
                ast::TypeOrExpr::Expr(_) => None,
            }
        }
        ast::AllNode::Typedef(ast) => {
            Some(cx.unpacked_type_from_ast(Ref(&ast.ty), Ref(&ast.dims), env, None))
        }
        ast::AllNode::ParamTypeDecl(ast) => {
            // Look for a parameter assignment in the param env.
            let env_data = cx.param_env_data(env);
            match env_data.find_type(ast.id()) {
                Some(ParamEnvBinding::Indirect(assigned_id)) => {
                    return cx.map_to_type(Ref(cx.ast_for_id(assigned_id.id())), assigned_id.env());
                }
                Some(ParamEnvBinding::Direct(t)) => return Some(t),
                _ => (),
            }

            // Look for a default assignment.
            if let Some(ref ty) = ast.ty {
                return Some(cx.packed_type_from_ast(Ref(ty), env, None));
            }

            // Otherwise complain.
            let d = DiagBuilder2::error(format!("{} not assigned and has no default", ast,));
            let contexts = cx.param_env_contexts(env);
            for &context in &contexts {
                cx.emit(
                    d.clone()
                        .span(cx.span(context))
                        .add_note("parameter declared here:")
                        .span(ast.human_span()),
                );
            }
            if contexts.is_empty() {
                cx.emit(d.span(ast.human_span()));
            }
            Some(UnpackedType::make_error())
        }
        _ => {
            debug!("{:#1?} does not map to a type", ast);
            None
        }
    }
}

/// Map a type node in the AST to an packed type.
///
/// This is the first half of type computation, and is concerned with the type
/// information that is usually carried on the left of a declaration name. In a
/// separate step, the declarations extend this packed type with the unpacked
/// dimensions provided on the right of the declaration name.
///
/// Note that this function nevertheless returns an `UnpackedType`, since the
/// AST can contain types like `string` and `event`, which don't map to the
/// `PackedType` struct.
///
/// If an implicit default is present, implicit types are expanded to that core
/// type. Otherwise the mapping fails with a diagnostic.
#[moore_derive::query]
pub(crate) fn packed_type_from_ast<'a>(
    cx: &impl Context<'a>,
    ast: Ref<'a, ast::Type<'a>>,
    env: ParamEnv,
    implicit_default: Option<ty::PackedCore<'a>>,
) -> &'a UnpackedType<'a> {
    let Ref(ast) = ast;
    let mut failed = false;
    use PackedOrUnpacked::*;

    // Map the type core.
    let mut ast_sign = ast.sign;
    let core = match ast.kind.data {
        ast::ImplicitType | ast::ImplicitSignedType | ast::ImplicitUnsignedType => {
            match implicit_default {
                Some(core) => Packed(core),
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!("cannot infer implicit type"))
                            .span(ast.span())
                            .add_note(
                                "This usually indicates that a declaration is missing a default \
                                 value.",
                            ),
                    );
                    error!("offending implicit type is {:#1?}", ast.kind);
                    return UnpackedType::make_error();
                }
            }
        }
        ast::VoidType => Packed(PackedCore::Void),

        // Integer vector types
        ast::BitType => Packed(PackedCore::IntVec(IntVecType::Bit)),
        ast::LogicType => Packed(PackedCore::IntVec(IntVecType::Logic)),
        ast::RegType => Packed(PackedCore::IntVec(IntVecType::Reg)),

        // Integer atom types
        ast::ByteType => Packed(PackedCore::IntAtom(IntAtomType::Byte)),
        ast::ShortIntType => Packed(PackedCore::IntAtom(IntAtomType::ShortInt)),
        ast::IntType => Packed(PackedCore::IntAtom(IntAtomType::Int)),
        ast::IntegerType => Packed(PackedCore::IntAtom(IntAtomType::Integer)),
        ast::LongIntType => Packed(PackedCore::IntAtom(IntAtomType::LongInt)),
        ast::TimeType => Packed(PackedCore::IntAtom(IntAtomType::Time)),

        // Real types
        ast::ShortRealType => Unpacked(UnpackedCore::Real(RealType::ShortReal)),
        ast::RealType => Unpacked(UnpackedCore::Real(RealType::Real)),
        ast::RealtimeType => Unpacked(UnpackedCore::Real(RealType::RealTime)),

        // Other unpacked types
        ast::StringType => Unpacked(UnpackedCore::String),
        ast::ChandleType => Unpacked(UnpackedCore::Chandle),
        ast::EventType => Unpacked(UnpackedCore::Event),

        // Struct types
        ast::StructType(ref strukt) => {
            // Assemble the struct type, with no members.
            let mut def = ty::StructType {
                ast: strukt,
                ast_type: ast,
                kind: strukt.kind,
                members: Default::default(),
                legacy_env: env,
            };

            // Populate the members.
            for member in &strukt.members {
                for name in &member.names {
                    // Depending on whether the struct is packed or unpacked, we
                    // admit packed or unpacked members types.
                    let ty = if strukt.packed {
                        cx.packed_type_from_ast(Ref(&member.ty), env, None)
                    } else {
                        cx.unpacked_type_from_ast(Ref(&member.ty), Ref(&name.dims), env, None)
                    };

                    def.members.push(ty::StructMember {
                        name: Spanned::new(name.name, name.span),
                        ty,
                        ast_member: member,
                        ast_name: name,
                    });
                }
            }

            // Keep track of the sign, and complain if the packed type itself
            // has separate sign information.
            if ast_sign != ast::TypeSign::None {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "`signed` or `unsigned` goes before the struct contents"
                    ))
                    .span(ast.span()),
                );
                failed = true;
            }
            ast_sign = strukt.signing;

            // Package up as packed or unpacked struct.
            if strukt.packed {
                Packed(PackedCore::Struct(def))
            } else {
                Unpacked(UnpackedCore::Struct(def))
            }
        }

        // Enum types
        ast::EnumType(ref enm) => {
            // Determine the base type, or default to int.
            let base = match enm.base_type {
                Some(ref ty) => {
                    let bty = cx.packed_type_from_ast(Ref(ty), env, None);
                    if bty.is_error() {
                        return UnpackedType::make_error();
                    }
                    if let Some(packed) = bty.get_packed() {
                        packed
                    } else {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "enum base type must be packed, but `{}` is unpacked",
                                bty
                            ))
                            .span(ty.span()),
                        );
                        return UnpackedType::make_error();
                    }
                }
                None => SbvType::nice(ty::Domain::TwoValued, ty::Sign::Signed, 32).to_packed(cx),
            };
            let base_explicit = enm.base_type.is_some();

            // Assemble the enum type.
            let def = ty::EnumType {
                ast: enm,
                base,
                base_explicit,
                variants: enm.variants.iter().map(|v| (v.name, v)).collect(),
            };

            // Package up.
            Packed(PackedCore::Enum(def))
        }

        // Named types
        ast::NamedType(name) => {
            // Resolve the name.
            let loc = cx.scope_location(ast);
            let def = match cx.resolve_local_or_error(name, loc, false) {
                Ok(def) => def,
                Err(()) => return UnpackedType::make_error(),
            };
            packed_type_from_def(cx, def, name.span, env)
        }

        // Scoped types
        ast::ScopedType {
            ref ty,
            member: false,
            name,
        } => match ty.kind.data {
            ast::NamedType(pkg_name) => {
                // Resolve the name.
                let loc = cx.scope_location(ty.as_ref());
                let def = match cx.resolve_local_or_error(pkg_name, loc, false) {
                    Ok(def) => def,
                    _ => return UnpackedType::make_error(),
                };

                // See if the binding is a package.
                let pkg = match def.node {
                    DefNode::Ast(node) => node.as_all().get_package(),
                    _ => None,
                };
                let pkg = match pkg {
                    Some(x) => x,
                    None => {
                        cx.emit(
                            DiagBuilder2::error(format!("`{}` is not a package", pkg_name))
                                .span(pkg_name.span)
                                .add_note(format!("`{}` was declared here:", pkg_name))
                                .span(def.node.span()),
                        );
                        return UnpackedType::make_error();
                    }
                };

                // Resolve the type name within the package.
                let def = match cx.resolve_hierarchical_or_error(name, pkg) {
                    Ok(def) => def,
                    _ => return UnpackedType::make_error(),
                };
                packed_type_from_def(cx, def, ast.span(), env)
            }
            _ => {
                cx.emit(
                    DiagBuilder2::error(format!("`{}` is not a package", ty.span().extract()))
                        .span(ty.span()),
                );
                return UnpackedType::make_error();
            }
        },
        ast::ScopedType { .. } => {
            cx.emit(
                DiagBuilder2::error(format!("`{}` is not a type", ast.span().extract()))
                    .span(ast.span()),
            );
            error!("Offending AST: {:#3?}", ast);
            return UnpackedType::make_error();
        }

        // Type references
        ast::TypeRef(ref arg) => {
            // Disambiguate if this is a `type(<type>)` or `type(<expr>)`.
            let arg = match cx.disamb_type_or_expr(Ref(arg)) {
                Ok(arg) => arg,
                Err(()) => return UnpackedType::make_error(),
            };
            let ty = match arg {
                ast::TypeOrExpr::Expr(expr) => cx.need_self_determined_type(expr.id(), env),
                ast::TypeOrExpr::Type(ty) => cx.packed_type_from_ast(Ref(ty), env, None),
            };

            // Distinguish between packed and unpacked types here.
            if let Some(ty) = ty.get_packed() {
                Packed(PackedCore::Ref {
                    span: ast.kind.span(),
                    ty,
                })
            } else {
                Unpacked(UnpackedCore::Ref {
                    span: ast.kind.span(),
                    ty,
                })
            }
        }

        ast::VirtIntfType { .. } | ast::MailboxType | ast::SpecializedType(..) => {
            bug_span!(ast.span(), cx, "type {:#1?} not implemented", ast.kind)
        }
    };

    let ty = match core {
        // Handle the packed case, which can still be extended by a sign and
        // packed dimensions.
        Packed(core) => {
            let sign = match ast_sign {
                ast::TypeSign::None => core.default_sign(),
                ast::TypeSign::Unsigned => ty::Sign::Unsigned,
                ast::TypeSign::Signed => ty::Sign::Signed,
            };
            let sign_explicit = ast_sign != ast::TypeSign::None;
            let mut dims = vec![];
            for dim in &ast.dims {
                match dim {
                    ast::TypeDim::Unsized => dims.push(ty::PackedDim::Unsized),
                    ast::TypeDim::Range(lhs, rhs) => {
                        match range_from_bounds_exprs(cx, lhs.id(), rhs.id(), env, ast.span()) {
                            Ok(r) => dims.push(ty::PackedDim::Range(r)),
                            Err(()) => {
                                failed = true;
                                continue;
                            }
                        }
                    }
                    _ => {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "unpacked dimension in the position of a packed dimension",
                            ))
                            .span(ast.span()),
                        );
                        failed = true;
                        continue;
                    }
                }
            }
            PackedType::make_sign_and_dims(cx, core, sign, sign_explicit, dims).to_unpacked(cx)
        }

        // Handle the unpacked case, where providing any sign or packed
        // dimension is invalid.
        Unpacked(core) => {
            if ast_sign != ast::TypeSign::None {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "unpacked type `{}` cannot be signed or unsigned",
                        core
                    ))
                    .span(ast.span()),
                );
                failed = true;
            }
            if !ast.dims.is_empty() {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "unpacked type `{}` cannot have packed dimensions",
                        core
                    ))
                    .span(ast.span()),
                );
                failed = true;
            }
            UnpackedType::make(cx, core)
        }
    };

    if failed {
        UnpackedType::make_error()
    } else {
        ty
    }
}

fn packed_type_from_def<'a>(
    cx: &impl Context<'a>,
    def: &'a resolver::Def<'a>,
    span: Span,
    env: ParamEnv,
) -> PackedOrUnpacked<'a> {
    use PackedOrUnpacked::*;

    // See if the binding is a type.
    let ty = match def.node {
        DefNode::Ast(node) => cx.map_to_type(Ref(node), env),
        _ => None,
    };
    let ty = match ty {
        Some(x) => x,
        None => {
            cx.emit(
                DiagBuilder2::error(format!("`{}` is not a type", def.name))
                    .span(span)
                    .add_note(format!("`{}` was declared here:", def.name))
                    .span(def.node.span()),
            );
            return Packed(PackedCore::Error);
        }
    };

    // Distinguish between packed and unpacked types here.
    if let Some(ty) = ty.get_packed() {
        Packed(PackedCore::Named { name: def.name, ty })
    } else {
        Unpacked(UnpackedCore::Named { name: def.name, ty })
    }
}

// A simple enum that keeps either a packed or unpacked core type.
enum PackedOrUnpacked<'a> {
    Packed(PackedCore<'a>),
    Unpacked(UnpackedCore<'a>),
}

/// Map a type node and unpacked dimensions in the AST to an unpacked type.
///
/// This is the second half of type computation. Maps the given type to a packed
/// type first, then applies the given dimensions as unpacked dimensions.
///
/// If an implicit default is present, implicit types are expanded to that core
/// type. Otherwise the mapping fails with a diagnostic.
#[moore_derive::query]
pub(crate) fn unpacked_type_from_ast<'a>(
    cx: &impl Context<'a>,
    ast_type: Ref<'a, ast::Type<'a>>,
    ast_dims: Ref<'a, [ast::TypeDim<'a>]>,
    env: ParamEnv,
    implicit_default: Option<ty::PackedCore<'a>>,
) -> &'a UnpackedType<'a> {
    // Map the type itself.
    let ty = cx.packed_type_from_ast(ast_type, env, implicit_default);

    // Apply unpacked dimensions.
    let mut failed = false;
    let Ref(ast_dims) = ast_dims;
    let mut dims = vec![];
    for dim in ast_dims {
        match dim {
            ast::TypeDim::Unsized => dims.push(ty::UnpackedDim::Unsized),
            ast::TypeDim::Expr(size) => {
                match size_from_bounds_expr(cx, size.id(), env, ast_type.span()) {
                    Ok(s) => dims.push(ty::UnpackedDim::Array(s)),
                    Err(()) => {
                        failed = true;
                        continue;
                    }
                }
            }
            ast::TypeDim::Range(lhs, rhs) => {
                match range_from_bounds_exprs(cx, lhs.id(), rhs.id(), env, ast_type.span()) {
                    Ok(r) => dims.push(ty::UnpackedDim::Range(r)),
                    Err(()) => {
                        failed = true;
                        continue;
                    }
                }
            }
            ast::TypeDim::Queue(Some(init_size)) => {
                match size_from_bounds_expr(cx, init_size.id(), env, ast_type.span()) {
                    Ok(s) => dims.push(ty::UnpackedDim::Queue(Some(s))),
                    Err(()) => {
                        failed = true;
                        continue;
                    }
                }
            }
            ast::TypeDim::Queue(None) => dims.push(ty::UnpackedDim::Queue(None)),
            ast::TypeDim::Associative(Some(ty)) => {
                let ty = cx.packed_type_from_ast(Ref(ty), env, None);
                if ty.is_error() {
                    failed = true;
                }
                dims.push(ty::UnpackedDim::Assoc(Some(ty)));
            }
            ast::TypeDim::Associative(None) => dims.push(ty::UnpackedDim::Assoc(None)),
        }
    }

    // Return either an error, the unmodified type, or the type with the
    // unpacked dimensions added.
    if failed {
        UnpackedType::make_error()
    } else if dims.is_empty() {
        ty
    } else {
        let mut ty = ty.clone();
        ty.dims.extend(dims);
        ty.intern(cx)
    }
}

/// Determine the type of an expression.
#[moore_derive::query]
pub(crate) fn type_of_expr<'a>(
    cx: &impl Context<'a>,
    expr: Ref<'a, hir::Expr<'a>>,
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
        | hir::ExprKind::LocalIntfSignal { .. }
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
        HirNode::Expr(e) => Some(cx.cast_expr_type(Ref(e), env)),
        _ => None,
    }
}

/// Get the cast type of an expression.
#[moore_derive::query]
pub(crate) fn cast_expr_type<'a>(
    cx: &impl Context<'a>,
    Ref(expr): Ref<'a, hir::Expr<'a>>,
    env: ParamEnv,
) -> CastType<'a> {
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
    expr: &'gcx hir::Expr<'gcx>,
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
    if let TypeContext::Type(ty) = context {
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
        TypeContext::Bool => {
            trace!("  Casting to bool ({})", context.ty());
            cast.add_cast(CastOp::Bool, context.ty());
            return cast;
        }
        TypeContext::Type(ty) => ty,
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
    expr: &'gcx hir::Expr<'gcx>,
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
        hir::ExprKind::Cast(ty, _) => Some(cx.packed_type_from_ast(
            Ref(cx.ast_for_id(ty).as_all().get_type().unwrap()),
            env,
            None,
        )),

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
                .unwrap_or(UnpackedType::make_error()),
        ),

        // Interface signal accesses resolve to the type of the signal.
        hir::ExprKind::LocalIntfSignal { inst, name } => Some(
            cx.type_of(inst.id(), env)
                .map(|ty| ty.get_interface().unwrap())
                .and_then(|intf| cx.resolve_hierarchical_or_error(name, intf))
                .map(|def| def.node.id())
                .and_then(|def| cx.type_of(def, env))
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
                        Some(retty_id) => Ok(cx.packed_type_from_ast(
                            Ref(cx.ast_for_id(retty_id).as_all().get_type().unwrap()),
                            env,
                            None,
                        )),
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
                            DiagBuilder2::error(format!(
                                "cannot index into a value of type `{}`",
                                target_ty
                            ))
                            .span(expr.span)
                            .add_note(format!(
                                "`{}` must be an array or have a simple bit-vector type \
                                 representation",
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
) -> Option<TypeContext<'a>> {
    let hir_id = cx.parent_node_id(onto).unwrap();
    let hir = match cx.hir_of(hir_id) {
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
        HirNode::IntPort(p) => match p.data {
            Some(ref v) if v.default == Some(onto) && !v.ty.is_implicit() => {
                Some(cx.type_of_int_port(Ref(p), env).into())
            }
            _ => None,
        },
        HirNode::VarDecl(v) if v.init == Some(onto) => {
            let ty = cx.ast_for_id(v.ty).as_all().get_type().unwrap();
            if !ty.is_implicit() {
                Some(
                    cx.type_of(hir_id, env)
                        .unwrap_or(UnpackedType::make_error())
                        .into(),
                )
            } else {
                None
            }
        }
        HirNode::ValueParam(v) if v.default == Some(onto) => {
            let ty = cx.ast_for_id(v.ty).as_all().get_type().unwrap();
            if !ty.is_implicit() {
                Some(
                    cx.type_of(hir_id, env)
                        .unwrap_or(UnpackedType::make_error())
                        .into(),
                )
            } else {
                None
            }
        }
        HirNode::Inst(inst) => {
            let details = cx.inst_details(Ref(inst), env).ok()?;
            details
                .ports
                .reverse_find(onto)
                .map(|id| {
                    trace!(
                        "Need to look up type of port {:?} {:?}, imposed on {:?}",
                        id,
                        details.inner_env,
                        onto
                    );
                    cx.type_of_ext_port(Ref(id), details.inner_env)
                })
                .map(Into::into)
        }
        HirNode::InstTarget(inst) => {
            let details = cx.inst_target_details(Ref(inst), env).ok()?;
            details
                .params
                .reverse_find_value(onto)
                .and_then(|param_id| cx.type_of(param_id, details.inner_env).ok())
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
) -> TypeContext<'a> {
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
    Type(&'a ty::UnpackedType<'a>),
    /// The surroundings ask for implicit boolean mapping (not truncation).
    Bool,
}

impl<'a> TypeContext<'a> {
    /// Convert the type context to an actual type.
    ///
    /// This resolves implicit boolean casts to the `logic` type.
    pub fn ty(&self) -> &'a ty::UnpackedType<'a> {
        match *self {
            TypeContext::Type(t) => t,
            TypeContext::Bool => ty::UnpackedType::make_logic(),
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

impl<'a> From<&'a ty::UnpackedType<'a>> for TypeContext<'a> {
    fn from(ty: &'a ty::UnpackedType<'a>) -> Self {
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

/// Get the type context imposed by an expression.
///
/// Determine the type context `expr` imposes on `onto`.
fn type_context_imposed_by_expr<'gcx>(
    cx: &impl Context<'gcx>,
    onto: NodeId,
    expr: &'gcx hir::Expr<'gcx>,
    env: ParamEnv,
) -> Option<TypeContext<'gcx>> {
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
            hir::UnaryOp::LogicNot => Some(TypeContext::Bool),

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
            hir::BinaryOp::LogicAnd | hir::BinaryOp::LogicOr => Some(TypeContext::Bool),

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
        hir::ExprKind::Ternary(cond, _, _) if onto == cond => Some(TypeContext::Bool),

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
        hir::ExprKind::PositionalPattern(ref nodes)
        | hir::ExprKind::RepeatPattern(_, ref nodes)
            if nodes.contains(&onto) =>
        {
            type_context_imposed_by_pattern(cx, onto, expr, env)
        }
        hir::ExprKind::NamedPattern(ref nodes) => {
            if nodes.iter().any(|&(_, n)| n == onto) {
                type_context_imposed_by_pattern(cx, onto, expr, env)
            } else {
                None
            }
        }

        // The `inside` expression imposes its operation type as type context.
        hir::ExprKind::Inside(..) => Some(cx.need_operation_type(expr.id, env).into()),

        // Bit- and part-select expressions impose their operation type as type
        // context.
        hir::ExprKind::Index(target, _) if onto == target => {
            let opty = cx.need_operation_type(expr.id, env);
            debug!(
                "Imposing operation type `{}` on `{}`",
                opty,
                cx.span(target).extract()
            );
            Some(opty.into())
        }

        _ => None,
    }
}

// Determine the type context a pattern expression imposes on its arguments.
// Only call this for `onto` that are strictly outside of potential field index
// expressions, i.e. not on the left of any `:` in the pattern.
fn type_context_imposed_by_pattern<'gcx>(
    cx: &impl Context<'gcx>,
    onto: NodeId,
    expr: &'gcx hir::Expr<'gcx>,
    env: ParamEnv,
) -> Option<TypeContext<'gcx>> {
    let map = match cx.map_pattern(Ref(expr), env) {
        Ok(x) => x,
        _ => return Some(UnpackedType::make_error().into()),
    };

    // Determine the types of the fields where the `onto` expression is
    // assigned.
    let tys: HashSet<_> = map
        .fields
        .iter()
        .flat_map(|(field, expr)| {
            if expr.id == onto {
                Some(field.ty(cx))
            } else {
                None
            }
        })
        .collect();

    // If the type is unique, we impose that as a constraint. Otherwise
    // we can't decide and just return.
    if tys.len() == 1 {
        Some(tys.into_iter().next().unwrap().into())
    } else {
        trace!(
            "Expression `{}` assigned to multiple fields with distinct types; no context imposed",
            expr.span().extract()
        );
        None
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
) -> Option<TypeContext<'gcx>> {
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
        hir::StmtKind::If { cond, .. } if onto == cond => Some(TypeContext::Bool),

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
                    Some(TypeContext::Bool)
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

fn size_from_bounds_expr<'a>(
    cx: &impl Context<'a>,
    expr: NodeId,
    env: ParamEnv,
    span: Span,
) -> Result<usize> {
    let size = match cx.constant_value_of(expr, env)?.kind {
        ValueKind::Int(ref int, ..) => int,
        ValueKind::Error => return Err(()),
        _ => {
            let span = cx.span(expr);
            cx.emit(
                DiagBuilder2::error(format!(
                    "array bound `{}` is not an integer",
                    span.extract()
                ))
                .span(span),
            );
            return Err(());
        }
    };
    let size = match size.to_usize() {
        Some(i) => i,
        None => {
            cx.emit(
                DiagBuilder2::error(format!("{} is too large", span.extract()))
                    .span(span)
                    .add_note(format!("array would contain {} elements", size)),
            );
            return Err(());
        }
    };
    Ok(size)
}

fn range_from_bounds_exprs<'a>(
    cx: &impl Context<'a>,
    lhs: NodeId,
    rhs: NodeId,
    env: ParamEnv,
    span: Span,
) -> Result<ty::Range> {
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
                DiagBuilder2::error(format!("{} is too large", span.extract()))
                    .span(span)
                    .add_note(format!("array would contain {} elements", size)),
            );
            return Err(());
        }
    };
    let offset = lo.to_isize().unwrap();
    Ok(ty::Range { size, dir, offset })
}
