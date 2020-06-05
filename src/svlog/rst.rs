// Copyright (c) 2016-2020 Fabian Schuiki

//! A resolved syntax tree.
//!
//! This module implements the RST, which is an unambiguous representation of
//! the AST. This is achieved by resolving AST ambiguities through name lookups.

use crate::crate_prelude::*;
use crate::{ast, ast_map::AstNode, common::arenas::Alloc};

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
                        ty.link_attach(expr);
                        cx.map_ast_with_parent(AstNode::Type(ty), ty.id());
                        Ok(cx.arena().alloc(ast::TypeOrExpr::Type(ty)))
                    }
                }
            }
            _ => Ok(ast),
        },
        ast::TypeOrExpr::Type(_ty) => Ok(ast),
    }
}
