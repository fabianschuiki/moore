// Copyright (c) 2016-2021 Fabian Schuiki

//! A resolved syntax tree.
//!
//! This module implements the RST, which is an unambiguous representation of
//! the AST. This is achieved by resolving AST ambiguities through name lookups.

use crate::crate_prelude::*;
use crate::{ast, ast_map::AstNode, common::arenas::Alloc, resolver::DefNode};

/// A node kind.
///
/// Nodes in the AST can be queried for their kind, which yields this enum.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    /// This node is a value.
    Value,
    /// This node is a type.
    Type,
}

/// Determine the kind of a node.
#[moore_derive::query]
pub(crate) fn disamb_kind<'a>(
    _cx: &impl Context<'a>,
    Ref(ast): Ref<'a, dyn ast::AnyNode<'a>>,
) -> Kind {
    match ast.as_all() {
        ast::AllNode::Type(..) | ast::AllNode::ParamTypeDecl(..) | ast::AllNode::Typedef(..) => {
            Kind::Type
        }
        _ => Kind::Value,
    }
}

/// Disambiguate a type or expression.
#[moore_derive::query]
pub(crate) fn disamb_type_or_expr<'a>(
    cx: &impl Context<'a>,
    Ref(ast): Ref<'a, ast::TypeOrExpr<'a>>,
) -> Result<&'a ast::TypeOrExpr<'a>> {
    match *ast {
        ast::TypeOrExpr::Expr(expr) => match expr.data {
            ast::IdentExpr(n) => {
                let loc = cx.scope_location(expr);
                let binding = cx.resolve_local_or_error(n, loc, false)?;
                match cx.disamb_kind(Ref(&binding.node)) {
                    Kind::Value => Ok(ast),
                    Kind::Type => {
                        let ty = cx.arena().alloc(ast::Type::new(
                            expr.span,
                            ast::TypeData {
                                kind: ast::TypeKind::new(expr.span, ast::NamedType(n)),
                                sign: ast::TypeSign::None,
                                dims: vec![],
                            },
                        ));
                        ty.link_attach(expr, expr.order());
                        cx.register_ast(ty);
                        cx.map_ast_with_parent(AstNode::Type(ty), ty.id());
                        Ok(cx.arena().alloc(ast::TypeOrExpr::Type(ty)))
                    }
                }
            }

            // TODO: The following is an ugly duplicate of code which also lives
            // in typeck. This whole scoped name resolution thing should be a
            // distinct RST query which returns something like a rst::Path.
            ast::ScopeExpr(ref target, name) => match target.data {
                ast::IdentExpr(pkg_name) => {
                    // Resolve the name.
                    let loc = cx.scope_location(target.as_ref());
                    let def = match cx.resolve_local_or_error(pkg_name, loc, false) {
                        Ok(def) => def,
                        _ => return Err(()),
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
                            return Err(());
                        }
                    };

                    // Resolve the type name within the package.
                    let def = match cx.resolve_hierarchical_or_error(name, pkg) {
                        Ok(def) => def,
                        _ => return Err(()),
                    };
                    match cx.disamb_kind(Ref(&def.node)) {
                        Kind::Value => Ok(ast),
                        Kind::Type => {
                            let target_ty = ast::Type::new(
                                target.span,
                                ast::TypeData {
                                    kind: ast::TypeKind::new(expr.span, ast::NamedType(pkg_name)),
                                    sign: ast::TypeSign::None,
                                    dims: vec![],
                                },
                            );
                            let ty = cx.arena().alloc(ast::Type::new(
                                expr.span,
                                ast::TypeData {
                                    kind: ast::TypeKind::new(
                                        expr.span,
                                        ast::ScopedType {
                                            ty: Box::new(target_ty),
                                            member: false,
                                            name,
                                        },
                                    ),
                                    sign: ast::TypeSign::None,
                                    dims: vec![],
                                },
                            ));
                            ty.link_attach(expr, expr.order());
                            cx.register_ast(ty);
                            cx.map_ast_with_parent(AstNode::Type(ty), ty.id());
                            Ok(cx.arena().alloc(ast::TypeOrExpr::Type(ty)))
                        }
                    }
                }
                _ => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "`{}` is not a package",
                            expr.span().extract()
                        ))
                        .span(expr.span()),
                    );
                    return Err(());
                }
            },
            _ => Ok(ast),
        },
        ast::TypeOrExpr::Type(_ty) => Ok(ast),
    }
}

/// Resolve the type/name ambiguity in a subroutine port.
#[moore_derive::query]
pub(crate) fn resolve_subroutine_port_ty_name<'a>(
    cx: &impl Context<'a>,
    Ref(node): Ref<'a, ast::SubroutinePort<'a>>,
) -> &'a (ast::Type<'a>, Option<ast::SubroutinePortName<'a>>) {
    let xs = match &node.ty_name {
        ast::Ambiguous::Unique(x) => return x,
        ast::Ambiguous::Ambiguous(xs) => xs,
    };
    debug!("Resolving ambiguity in {:1?}", node);

    // Let's first try to resolve type names.
    for x in xs {
        let name = match x.0.kind.data {
            ast::NamedType(x) => x,
            _ => continue,
        };
        trace!(" - Trying type name {}", name);
        let binding = match cx
            .resolve_local(name.value, cx.scope_location(node), false)
            .unwrap_or(None)
        {
            Some(x) => x,
            None => continue,
        };
        trace!(" - Resolved to {:?}", binding);
        match cx.disamb_kind(Ref(&binding.node)) {
            Kind::Type => {
                trace!(" - Resolved as {:?}", x);
                return x;
            }
            _ => continue,
        }
    }

    // If we arrive here, named types did not match. Return whatever is left.
    for x in xs {
        if x.1.is_some() {
            trace!(" - Resolved as {:?}", x);
            return x;
        }
    }

    bug_span!(node.span, cx, "unable to resolve ambiguity");
}
