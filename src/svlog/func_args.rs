// Copyright (c) 2016-2020 Fabian Schuiki

//! A list of arguments to a function or task, with different styles resolved.
//!
//! This module simplifies the list of arguments of a function or task. This is
//! necessary since SystemVerilog allows for two distinct styles of declaring
//! the function arguments, which are similar to the ANSI and non-ANSI port list
//! styles for modules. Essentially, the arguments can be declared in the
//! function prototype directly, or as part of the function body (at the very
//! top).
//!
//! More concretely, it does the following:
//!
//! - Canonicalize ANSI/non-ANSI style
//! - Fill in implicit argument details (defaults and carried-over from
//!   previous argument)
//!
//! Note that when this module refers to "functions", it generally means both
//! *functions* and *tasks*.

use crate::crate_prelude::*;
use crate::{ast_map::AstNode, common::arenas::Alloc};
use std::borrow::Cow;

/// A list of arguments of a function or task.
#[derive(Debug, PartialEq, Eq)]
pub struct FuncArgList<'a> {
    /// The function or task containing this argument.
    pub func: &'a ast::SubroutineDecl<'a>,
    /// The canonicalized arguments of the function or task.
    pub args: Vec<FuncArg<'a>>,
}

/// An function or task argument.
#[derive(Debug, PartialEq, Eq)]
pub struct FuncArg<'a> {
    /// The node that spawned this argument.
    pub ast: &'a dyn ast::AnyNode<'a>,
    /// The function or task containing this argument.
    pub func: &'a ast::SubroutineDecl<'a>,
    /// Location of the argument declaration in the source file.
    pub span: Span,
    /// Name of the argument. May be `None` if the argument is part of a
    /// prototype declaration.
    pub name: Option<Spanned<Name>>,
    /// Direction of the argument.
    pub dir: ast::SubroutinePortDir,
    /// Data type of the argument.
    pub ty: &'a ast::Type<'a>,
    /// Unpacked dimensions of the argument.
    pub unpacked_dims: &'a [ast::TypeDim<'a>],
    /// Whether an explicit `var` was present.
    pub var: bool,
    /// Optional default value assigned to the argument if left unassigned.
    pub default: Option<&'a ast::Expr<'a>>,
}

/// Resolve the arguments of a function or task a canonical list.
#[moore_derive::query]
pub(crate) fn canonicalize_func_args<'a>(
    cx: &impl Context<'a>,
    node: &'a ast::SubroutineDecl<'a>,
) -> &'a FuncArgList<'a> {
    debug!("Building port list of {:?}", node);
    let mut next_rib = node.id(); // TODO(fschuiki): Remove once NodeIds no longer needed

    // If an argument list has been provided (`foo(...);`), use that to gather
    // the list of arguments. If not (`foo;`), scan the function body for
    // argument declarations.
    let args = if let Some(ref args) = node.prototype.args {
        trace!("Uses ANSI style");
        gather_from_args(cx, node, args, next_rib)
    } else {
        trace!("Uses non-ANSI style");
        gather_from_items(cx, node, &node.items, next_rib)
    };

    // Package the argument list up.
    let list = FuncArgList { func: node, args };
    trace!("Argument list of {:?} is: {:#?}", node, list);
    cx.gcx().arena.alloc_func_arg_list(list)
}

/// Gather a list of arguments from the arguments in the function declaration.
fn gather_from_args<'a>(
    cx: &impl Context<'a>,
    node: &'a ast::SubroutineDecl<'a>,
    args: &'a [ast::SubroutinePort<'a>],
    next_rib: NodeId,
) -> Vec<FuncArg<'a>> {
    let mut out_args = vec![];
    let first_span = args.get(0).map(|x| x.span()).unwrap_or(node.span());

    // Determine the default direction and data type. These *may* be carried
    // over from argument to argument.
    let mut carry_dir = ast::SubroutinePortDir::Input;
    let mut carry_ty = Cow::Owned(ast::TypeKind::new(
        first_span.begin().into(),
        ast::LogicType,
    ));
    let mut carry_sign = ast::TypeSign::None;
    let mut carry_packed_dims: &[ast::TypeDim] = &[];

    for arg in args {
        // First resolve the ambiguity in the port type and name.
        let (ty, name) = cx.resolve_subroutine_port_ty_name(Ref(arg));

        // If no direction has been provided, use the one carried over from the
        // previous argument.
        let dir = arg.dir.unwrap_or(carry_dir);

        // Explicitly stating the port resets the carried-over data type.
        if arg.dir.is_some() {
            carry_ty = Cow::Owned(ast::TypeKind::new(
                first_span.begin().into(),
                ast::LogicType,
            ));
            carry_sign = ast::TypeSign::None;
            carry_packed_dims = &[];
        }

        // If no data type, sign, or packed dimensions have been provided, use
        // the ones carried over from the previous argument. Otherwise we use
        // the ones provided, filling in an implicit base data type if needed.
        let inherit = ty.kind.data == ast::ImplicitType
            && ty.sign == ast::TypeSign::None
            && ty.dims.is_empty();

        let (ty, sign, packed_dims, ty_span) = if inherit {
            (carry_ty, carry_sign, carry_packed_dims, None)
        } else {
            // If the argument has an implicit data type, use the one carried
            // over from before.
            let kind = if ty.kind.data == ast::ImplicitType {
                carry_ty
            } else {
                Cow::Borrowed(&ty.kind)
            };
            (kind, ty.sign, ty.dims.as_slice(), Some(ty.span()))
        };

        // Keep the direction, type, sign, and packed dimensions around for the
        // next argument in the list, which might want to inherit them.
        carry_dir = dir;
        carry_ty = ty.clone();
        carry_sign = sign;
        carry_packed_dims = packed_dims;

        // Wrap the type up.
        let ty = cx.arena().alloc(ast::Type::new(
            ty_span.unwrap_or(arg.span()),
            ast::TypeData {
                kind: ty.into_owned(),
                sign: sign,
                dims: packed_dims.to_vec(),
            },
        ));
        ty.link_attach(arg, arg.order());
        cx.register_ast(ty);
        cx.map_ast_with_parent(AstNode::Type(ty), next_rib);

        // Extract the name and default value for the argument.
        let (name, unpacked_dims, default): (_, &[_], _) = match name {
            Some(pn) => (Some(pn.name), pn.dims.as_slice(), pn.expr.as_ref()),
            None => (None, &[], None),
        };

        // Add an argument to the list.
        out_args.push(FuncArg {
            ast: arg,
            func: node,
            span: arg.span,
            name,
            dir,
            ty,
            var: arg.var,
            unpacked_dims,
            default,
        });
    }

    out_args
}

/// Gather a list of arguments from the port declarations in a function body.
fn gather_from_items<'a>(
    cx: &impl Context<'a>,
    node: &'a ast::SubroutineDecl<'a>,
    items: &'a [ast::SubroutineItem<'a>],
    next_rib: NodeId,
) -> Vec<FuncArg<'a>> {
    let mut args = vec![];
    let mut non_port = None;
    let mut non_port_reported = false;

    for item in items {
        // Only consider port declarations.
        let port = match item {
            ast::SubroutineItem::PortDecl(x) => x,
            ast::SubroutineItem::Stmt(x) => {
                non_port = Some(non_port.unwrap_or(x));
                continue;
            }
        };

        // Emit a warning if ports and statements are interleaved.
        if let Some(non_port) = non_port {
            if !non_port_reported {
                cx.emit(
                    DiagBuilder2::warning(format!("port after statement"))
                        .span(port.span())
                        .add_note("Port declaration appears after this statement:")
                        .span(non_port.span())
                        .add_note(
                            "This is accepted by moore, but is forbidden according to IEEE \
                             1800-2017 where all ports must appear before regular statements.",
                        ),
                );
                non_port_reported = true;
            }
        }

        // Determine the data type. If it is an implicit type, default to
        // `logic`.
        let ty: &_ = if port.ty.kind.data == ast::ImplicitType {
            let ty = cx.arena().alloc(ast::Type::new(
                port.ty.span(),
                ast::TypeData {
                    kind: ast::TypeKind::new(port.ty.span(), ast::LogicType),
                    sign: port.ty.sign,
                    dims: port.ty.dims.clone(),
                },
            ));
            ty.link_attach(port, port.order());
            cx.register_ast(ty);
            cx.map_ast_with_parent(AstNode::Type(ty), next_rib);
            ty
        } else {
            &port.ty
        };

        // Add an argument to the list for every declared port name.
        for name in &port.names {
            args.push(FuncArg {
                ast: port,
                func: node,
                span: port.span,
                name: Some(Spanned::new(name.name, name.span)),
                dir: port.dir,
                ty,
                var: port.var,
                unpacked_dims: &name.dims,
                default: name.init.as_ref(),
            });
        }
    }

    args
}

/// A visitor that emits diagnostics for canonicalized function argument lists.
pub struct FuncArgsVerbosityVisitor<'cx, C> {
    cx: &'cx C,
}

impl<'cx, C> FuncArgsVerbosityVisitor<'cx, C> {
    /// Create a new name resolution visitor.
    pub fn new(cx: &'cx C) -> Self {
        FuncArgsVerbosityVisitor { cx }
    }
}

impl<'a, 'cx, C> ast::Visitor<'a> for FuncArgsVerbosityVisitor<'cx, C>
where
    C: Context<'a>,
    'a: 'cx,
{
    fn pre_visit_subroutine_decl(&mut self, node: &'a ast::SubroutineDecl<'a>) -> bool {
        let list = self.cx.canonicalize_func_args(node);
        let mut d = DiagBuilder2::note("canonicalized subroutine arguments")
            .span(node.span())
            .add_note(format!(
                "Subroutine `{}` has the following arguments:",
                node.prototype.name
            ));
        for arg in &list.args {
            let name = match arg.name {
                Some(name) => format!(" {}", name),
                None => format!(""),
            };
            let ty = self.cx.unpacked_type_from_ast(
                Ref(arg.ty),
                Ref(arg.unpacked_dims),
                self.cx.default_param_env(),
                None,
            );
            d = d.add_note(format!("{} {}{}", arg.dir, ty, name));
        }
        self.cx.emit(d);
        true
    }
}
