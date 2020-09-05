// Copyright (c) 2016-2020 Fabian Schuiki

//! A list of ports on a node, with ANSI/non-ANSI styles resolved.
//!
//! This module implements the port analysis required to determine if a node
//! uses an ANSI or non-ANSI port list, and to match up ports with other bits
//! and pieces in the node body. It produces separate, clean-cut internal and
//! external views of the port list.
//!
//! More concretely, it does the following:
//!
//! - Detect ANSI/non-ANSI style
//! - Fill in implicit port details (defaults and carried-over from previous)
//! - Combine port declarations in the node body with var/net declarations
//! - Build internal port list (visible from within the node)
//! - Parse port expressions into an external port list (visible when
//!   instantiating the node)

// TODO: This should eventually be moved into the `syntax` crate, as soon as the
// only thing we really need from the `Context` is ID allocation (no more AST
// mapping business).

use crate::crate_prelude::*;
use crate::{ast_map::AstNode, common::arenas::Alloc};
use std::{
    borrow::Cow,
    collections::HashMap,
    hash::{Hash, Hasher},
};

/// List of internal and external ports of a node.
///
/// A `PortList` consists of an ordered list of internal and external ports. The
/// external ports map to one or more internal ports via `PortExpr`. An optional
/// name lookup table allows for external ports to be connected to by name.
#[derive(Debug, PartialEq, Eq)]
pub struct PortList<'a> {
    /// The internal ports.
    pub int: Vec<IntPort<'a>>,
    /// The external ports, in order for positional connections. Port indices
    /// are indices into `int`.
    pub ext_pos: Vec<ExtPort<'a>>,
    /// The external ports, for named connections. Values are indices into
    /// `ext_pos`. `None` if there are any purely positional external ports.
    pub ext_named: Option<HashMap<Name, usize>>,
    /// The last rib in the list. Useful for name resolution. Obsoleted by new
    /// resolver.
    pub(crate) tail_rib: NodeId,
}

/// An internal port.
#[derive(Debug, PartialEq, Eq)]
pub struct IntPort<'a> {
    /// Node ID of the port.
    pub id: NodeId,
    /// The AST node that spawned this port.
    pub ast: &'a dyn ast::AnyNode<'a>,
    /// The node containing the port.
    pub node: &'a dyn PortedNode<'a>,
    /// Location of the port declaration in the source file.
    pub span: Span,
    /// Name of the port.
    pub name: Spanned<Name>,
    /// Direction of the port.
    pub dir: ast::PortDir,
    /// Kind of the port.
    pub kind: ast::VarKind,
    /// Additional port details. Omitted if this is an explicitly-named ANSI
    /// port, and the port details must be inferred from declarations inside the
    /// node.
    pub data: Option<IntPortData<'a>>,
}

/// Additional internal port details.
#[derive(Debug, PartialEq, Eq)]
pub struct IntPortData<'a> {
    /// Type of the port.
    pub ty: &'a ast::Type<'a>,
    /// Unpacked dimensions of the port.
    pub unpacked_dims: &'a [ast::TypeDim<'a>],
    /// Optional redundant type (possible in non-ANSI ports), which must be
    /// checked against `ty`.
    // TODO: Make this an AST reference.
    pub matching: Option<(NodeId, ())>,
    /// Optional default value assigned to the port if left unconnected.
    // TODO: Make this an AST reference.
    pub default: Option<NodeId>,
}

/// An external port.
#[derive(Debug, PartialEq, Eq)]
pub struct ExtPort<'a> {
    /// Node ID of the port.
    pub id: NodeId,
    /// The node containing the port.
    pub node: &'a dyn PortedNode<'a>,
    /// Location of the port declaration in the source file.
    pub span: Span,
    /// Optional name of the port.
    pub name: Option<Spanned<Name>>,
    /// Port expressions that map this external to internal ports. May be empty
    /// in case of a port that does not connect to anything.
    pub exprs: Vec<ExtPortExpr>,
}

/// A port expression associating an external port with an internal port.
#[derive(Debug, PartialEq, Eq)]
pub struct ExtPortExpr {
    /// Index of the internal port this expression targets.
    pub port: usize,
    /// Selects into the internal port.
    pub selects: Vec<ExtPortSelect>,
}

/// A select operation into an internal port.
#[derive(Debug, PartialEq, Eq)]
pub enum ExtPortSelect {
    /// Tombstone.
    Error,
    /// An indexing operation, like `[7:0]` or `[42]`.
    Index(hir::IndexMode),
}

impl HasSpan for IntPort<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for IntPort<'_> {
    fn desc(&self) -> &'static str {
        "port"
    }

    fn desc_full(&self) -> String {
        format!("port `{}`", self.name.value)
    }
}

impl HasSpan for ExtPort<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.map(|n| n.span).unwrap_or(self.span)
    }
}

impl HasDesc for ExtPort<'_> {
    fn desc(&self) -> &'static str {
        "port"
    }

    fn desc_full(&self) -> String {
        self.name
            .map(|n| format!("port `{}`", n))
            .unwrap_or_else(|| "port".to_string())
    }
}

/// Marker trait for AST nodes that have ports.
pub trait PortedNode<'a>: ast::AnyNode<'a> + resolver::ScopedNode<'a> {
    /// Get the ports of the node.
    fn ports(&self) -> &[ast::Port<'a>];

    /// Get the items of the node.
    fn items(&self) -> &[ast::Item<'a>];
}

impl<'a> PortedNode<'a> for ast::Module<'a> {
    fn ports(&self) -> &[ast::Port<'a>] {
        &self.ports
    }
    fn items(&self) -> &[ast::Item<'a>] {
        &self.items
    }
}

impl<'a> PortedNode<'a> for ast::Interface<'a> {
    fn ports(&self) -> &[ast::Port<'a>] {
        &self.ports
    }
    fn items(&self) -> &[ast::Item<'a>] {
        &self.items
    }
}

// Compare and hash `PortedNode` by reference for use in the query system.
impl<'a> Eq for &'a dyn PortedNode<'a> {}
impl<'a> PartialEq for &'a dyn PortedNode<'a> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.as_ptr(), other.as_ptr())
    }
}
impl<'a> Hash for &'a dyn PortedNode<'a> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        std::ptr::hash(self.as_ptr(), h)
    }
}

/// Anything that can be converted to a `PortedNode`.
pub trait AsPortedNode<'a> {
    /// Return this node as a `PortedNode`, or `None` if it generates no scope.
    fn get_ported(&self) -> Option<&'a dyn PortedNode<'a>>;

    /// Check if this node is a `PortedNode`.
    fn is_ported(&self) -> bool {
        self.get_ported().is_some()
    }
}

impl<'a> AsPortedNode<'a> for ast::AllNode<'a> {
    fn get_ported(&self) -> Option<&'a dyn PortedNode<'a>> {
        match *self {
            // This should reflect the impl trait list above!
            ast::AllNode::Module(x) => Some(x),
            ast::AllNode::Interface(x) => Some(x),
            _ => None,
        }
    }
}

/// Resolve the ports of a module or interface to a canonical list.
///
/// This is a fairly complex process due to the many degrees of freedom in SV.
/// Mainly we identify if the item uses an ANSI or non-ANSI style and then go
/// ahead and create the external and internal views of the ports.
#[moore_derive::query]
pub(crate) fn canonicalize_ports<'a>(
    cx: &impl Context<'a>,
    node: &'a dyn PortedNode<'a>,
) -> &'a PortList<'a> {
    debug!("Building port list of {:?}", node);
    let mut next_rib = node.id();
    let ast_ports = node.ports();
    let ast_items = node.items();

    // First determined if the node uses ANSI or non-ANSI style. We do this by
    // Determining whether the first port has type, sign, and direction omitted.
    // If it has, the ports are declared in non-ANSI style.
    let (nonansi, first_span) = {
        let first = match ast_ports.first() {
            Some(p) => p,
            None => {
                return cx.gcx().arena.alloc_port_list(PortList {
                    int: Default::default(),
                    ext_pos: Default::default(),
                    ext_named: Default::default(),
                    tail_rib: next_rib,
                })
            }
        };
        let nonansi = match first.data {
            ast::PortData::Explicit { ref dir, .. } if dir.is_none() => true,
            ast::PortData::Named {
                ref dir,
                ref kind,
                ref ty,
                ref expr,
                ..
            } if dir.is_none()
                && kind.is_none()
                && expr.is_none()
                && ty.kind.data == ast::ImplicitType
                && ty.sign == ast::TypeSign::None
                && ty.dims.is_empty() =>
            {
                true
            }
            ast::PortData::Implicit(_) => true,
            _ => false,
        };
        (nonansi, first.span())
    };
    debug!(
        "Module uses {} style",
        if nonansi { "non-ANSI" } else { "ANSI" }
    );

    // Create the external and internal port views.
    let partial_ports = match nonansi {
        true => lower_node_ports_nonansi(cx, ast_ports, ast_items, first_span, node),
        false => lower_node_ports_ansi(cx, ast_ports, ast_items, first_span, node),
    };
    trace!("Lowered ports: {:#?}", partial_ports);

    // Extend the internal port with default sign, port kind, and data type
    // where necessary in order to arrive at a final internal port list.
    let mut ports = vec![];
    let default_net_type = ast::NetType::Wire; // TODO: Make changeable by directive

    for port in partial_ports.int {
        let port_id = port.ast.id();

        // Determine the port kind.
        let kind = port.kind.unwrap_or_else(|| match port.dir {
            ast::PortDir::Input | ast::PortDir::Inout => ast::VarKind::Net {
                ty: default_net_type,
                kind: ast::NetKind::None,
            },
            ast::PortDir::Output => {
                if port.ty.data == ast::ImplicitType {
                    ast::VarKind::Net {
                        ty: default_net_type,
                        kind: ast::NetKind::None,
                    }
                } else {
                    ast::VarKind::Var
                }
            }
            ast::PortDir::Ref => ast::VarKind::Var,
        });

        // Verify that `inout` ports are of net kind, and `ref` ports are of var
        // kind.
        match (port.dir, kind) {
            (ast::PortDir::Inout, ast::VarKind::Var) => cx.emit(
                DiagBuilder2::error(format!(
                    "inout port `{}` must be a net; but is declared as variable",
                    port.name
                ))
                .span(port.name.span),
            ),
            (ast::PortDir::Ref, ast::VarKind::Net { .. }) => cx.emit(
                DiagBuilder2::error(format!(
                    "ref port `{}` must be a variable; but is declared as net",
                    port.name
                ))
                .span(port.name.span),
            ),
            _ => (),
        }

        // Hook things up in the hierarchy.
        cx.set_ast(port_id, AstNode::Port(port.span));
        cx.set_parent(port_id, next_rib);

        // Condense the details of this port, unless it is an inferred port
        // generated by an explicitly-named ANSI prot.
        let data = if port.inferred {
            None
        } else {
            // Determine the data type.
            let ty = if port.ty.data == ast::ImplicitType {
                Cow::Owned(ast::TypeKind::new(port.ty.span(), ast::LogicType))
            } else {
                port.ty
            };
            let ty = cx.arena().alloc(ast::Type::new(
                port.ty_span.unwrap_or(port.span),
                ast::TypeData {
                    kind: ty.into_owned(),
                    sign: port.sign,
                    dims: port.packed_dims.to_vec(),
                },
            ));
            ty.link_attach(port.ast, port.ast.order());
            cx.register_ast(ty);
            cx.map_ast_with_parent(AstNode::Type(ty), next_rib);

            // Allocate the default expression.
            let default = port
                .default
                .map(|expr| cx.map_ast_with_parent(AstNode::Expr(expr), port_id));

            // Everything following the port can see the port.
            next_rib = port_id;

            Some(IntPortData {
                ty,
                unpacked_dims: port.unpacked_dims,
                matching: None,
                default,
            })
        };

        // Package everything up in an internal port.
        ports.push(IntPort {
            id: port_id,
            ast: port.ast,
            node,
            span: port.span,
            name: port.name,
            dir: port.dir,
            kind,
            data,
        });
    }

    // Package the port list up.
    let list = PortList {
        int: ports,
        ext_pos: partial_ports.ext_pos,
        ext_named: partial_ports.ext_named,
        tail_rib: next_rib,
    };
    trace!("Port list of {:?} is: {:#?}", node, list);
    cx.gcx().arena.alloc_port_list(list)
}

/// Lower the ANSI ports of a node.
fn lower_node_ports_ansi<'a>(
    cx: &impl Context<'a>,
    ast_ports: &'a [ast::Port<'a>],
    ast_items: &'a [ast::Item<'a>],
    first_span: Span,
    node: &'a dyn PortedNode<'a>,
) -> PartialPortList<'a> {
    // Emit errors for any port declarations inside the node.
    for item in ast_items {
        let ast = match &item.data {
            ast::ItemData::PortDecl(pd) => pd,
            _ => continue,
        };
        cx.emit(
            DiagBuilder2::error(format!("port declaration in body of ANSI-style {:#}", node))
                .span(ast.span)
                .add_note(format!(
                    "A {:#} with an ANSI-style port list cannot have port declarations in the \
                     body.",
                    node
                ))
                .add_note("Consider using non-ANSI style.")
                .add_note("First port uses ANSI style:")
                .span(first_span),
        );
    }

    // Ports have a rather sticky way of tracking types, signs, dimensions, etc.
    // Keep a list of "carry" variables that carry over the previous port's
    // details over to the next port. Initialize with the default mandated by
    // the standard.
    let mut carry_dir = ast::PortDir::Inout;
    let mut carry_kind: Option<ast::VarKind> = None;
    let mut carry_ty = Cow::Owned(ast::TypeKind::new(
        first_span.begin().into(),
        ast::LogicType,
    ));
    let mut carry_sign = ast::TypeSign::None;
    let mut carry_packed_dims: &[ast::TypeDim] = &[];

    // Map each of the ports in the list.
    let mut int_ports: Vec<PartialPort> = vec![];
    let mut ext_pos: Vec<ExtPort> = vec![];
    let mut ext_named: HashMap<Name, usize> = HashMap::new();
    let mut explicit_named: HashMap<(ast::PortDir, Name), usize> = HashMap::new();

    for port in ast_ports {
        let port = match &port.data {
            // [direction] [net_type|"var"] type_or_implicit ident {dimension} ["=" expr]
            ast::PortData::Named {
                dir,
                kind,
                ty,
                name,
                dims: unpacked_dims,
                expr,
            } => {
                // If no direction has been provided, use the one carried over
                // from the previous port.
                let dir = dir.unwrap_or(carry_dir);

                // If no port kind has been provided, use the one carried over
                // from the previous port.
                let kind = kind.or(carry_kind);

                // If no port type has been provided, use the one carried over
                //  from the previous port.
                let (ty, sign, packed_dims, ty_span) = if ty.kind.data == ast::ImplicitType
                    && ty.sign == ast::TypeSign::None
                    && ty.dims.is_empty()
                {
                    (carry_ty, carry_sign, carry_packed_dims, None)
                } else {
                    (
                        Cow::Borrowed(&ty.kind),
                        ty.sign,
                        ty.dims.as_slice(),
                        Some(ty.span),
                    )
                };

                // Keep the direction, kind, and type around for the next port
                // in the list, which might want to inherit them.
                carry_dir = dir;
                carry_kind = kind;
                carry_ty = ty.clone();
                carry_sign = sign;
                carry_packed_dims = packed_dims;

                let data = PartialPort {
                    name: *name,
                    span: port.span,
                    ast: port,
                    kind,
                    dir,
                    sign,
                    ty,
                    ty_span,
                    packed_dims,
                    unpacked_dims,
                    default: expr.as_ref(),
                    inferred: false,
                    var_decl: None,
                    net_decl: None,
                    match_ty: None,
                };
                let ext_port = ExtPort {
                    id: cx.alloc_id(port.span()),
                    node,
                    span: port.span(),
                    name: Some(data.name),
                    exprs: vec![ExtPortExpr {
                        port: int_ports.len(),
                        selects: vec![],
                    }],
                };
                int_ports.push(data);
                ext_port
            }

            // [direction] "." ident "(" [expr] ")"
            ast::PortData::Explicit { dir, name, expr } => {
                // If no direction has been provided, use the one carried
                // over from the previous port.
                let dir = dir.unwrap_or(carry_dir);

                // Clear the carry to some sane default. Not sure if this is the
                // expected behaviour, but there are no further details in the
                // standard. What a joke.
                carry_dir = dir;
                carry_kind = None;
                carry_ty = Cow::Owned(ast::TypeKind::new(
                    port.span().begin().into(),
                    ast::LogicType,
                ));
                carry_sign = ast::TypeSign::None;
                carry_packed_dims = &[];

                // Map the expression to a port expression.
                let pe = match expr {
                    Some(expr) => lower_port_expr(cx, expr, node.id()),
                    None => vec![],
                };

                // Introduce inferred ports for each port reference in the port
                // expression.
                let pe = pe
                    .into_iter()
                    .map(|pr| {
                        let index =
                            *explicit_named
                                .entry((dir, pr.name.value))
                                .or_insert_with(|| {
                                    let index = int_ports.len();
                                    trace!("Adding inferred port {}", pr.name);
                                    int_ports.push(PartialPort {
                                        name: pr.name,
                                        span: port.span,
                                        ast: port,
                                        kind: None,
                                        dir,
                                        sign: ast::TypeSign::None,
                                        ty: Cow::Owned(ast::TypeKind::new(
                                            port.span().begin().into(),
                                            ast::ImplicitType,
                                        )), // inferred from expression
                                        ty_span: None,
                                        packed_dims: &[], // inferred from expression
                                        unpacked_dims: &[],
                                        default: None,
                                        inferred: true,
                                        var_decl: None,
                                        net_decl: None,
                                        match_ty: None,
                                    });
                                    index
                                });
                        ExtPortExpr {
                            port: index,
                            selects: pr.selects,
                        }
                    })
                    .collect();

                ExtPort {
                    id: cx.alloc_id(port.span()),
                    node,
                    span: port.span(),
                    name: Some(*name),
                    exprs: pe,
                }
            }

            _ => {
                cx.emit(
                    DiagBuilder2::error("non-ANSI port in ANSI port list")
                        .span(port.span())
                        .add_note("First port uses ANSI style:")
                        .span(first_span),
                );
                error!("Invalid port: {:?}", port);
                continue;
            }
        };

        // Build a map of ordered and named port associations.
        if let Some(prev) = ext_named.insert(port.name.unwrap().value, ext_pos.len()) {
            cx.emit(
                DiagBuilder2::error(format!(
                    "port `{}` declared multiple times",
                    port.name.unwrap().value
                ))
                .span(port.name.unwrap().span)
                .add_note("Previous declaration was here:")
                .span(ext_pos[prev].name.unwrap().span),
            );
        }

        // Add the port to the internal and external port list.
        ext_pos.push(port);
    }

    PartialPortList {
        int: int_ports,
        ext_pos,
        ext_named: Some(ext_named),
    }
}

/// Lower the non-ANSI ports of a node.
fn lower_node_ports_nonansi<'a>(
    cx: &impl Context<'a>,
    ast_ports: &'a [ast::Port<'a>],
    ast_items: &'a [ast::Item<'a>],
    first_span: Span,
    node: &'a dyn PortedNode<'a>,
) -> PartialPortList<'a> {
    // As a first step, collect the ports declared inside the node body. These
    // will form the internal view of the ports.
    let mut decl_order: Vec<PartialPort> = vec![];
    let mut decl_names = HashMap::new();
    for item in ast_items {
        let ast = match &item.data {
            ast::ItemData::PortDecl(pd) => pd,
            _ => continue,
        };
        // trace!("Found {:#?}", ast);
        for name in &ast.names {
            let data = PartialPort {
                span: ast.span,
                name: Spanned::new(name.name, name.name_span),
                ast: name,
                kind: ast.kind,
                dir: ast.dir,
                sign: ast.ty.sign,
                ty: Cow::Borrowed(&ast.ty.kind),
                ty_span: Some(ast.ty.span),
                packed_dims: &ast.ty.dims,
                unpacked_dims: &name.dims,
                default: name.init.as_ref(),
                inferred: false,
                match_ty: None,
                var_decl: None,
                net_decl: None,
            };
            // trace!("Producing {:#?}", data);
            let index = decl_order.len();
            if let Some(prev) = decl_names.insert(data.name.value, index) {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "port `{}` declared multiple times",
                        data.name.value
                    ))
                    .span(data.name.span)
                    .add_note("Previous declaration was here:")
                    .span(decl_order[prev].name.span),
                );
            }
            decl_order.push(data);
        }
    }

    // As a second step, collect the variable and net declarations inside the
    // node body which further specify a port.
    for item in ast_items {
        match &item.data {
            ast::ItemData::VarDecl(vd) => {
                for name in &vd.names {
                    let index = match decl_names.get(&name.name) {
                        Some(&e) => e,
                        None => continue,
                    };
                    let entry = &mut decl_order[index];
                    if let Some(prev) = std::mem::replace(&mut entry.var_decl, Some((vd, name))) {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "port variable `{}` declared multiple times",
                                name.name
                            ))
                            .span(name.name_span)
                            .add_note("previous declaration was here:")
                            .span(prev.1.name_span),
                        );
                    }
                }
            }
            ast::ItemData::NetDecl(nd) => {
                for name in &nd.names {
                    let index = match decl_names.get(&name.name) {
                        Some(&e) => e,
                        None => continue,
                    };
                    let entry = &mut decl_order[index];
                    if let Some(prev) = std::mem::replace(&mut entry.net_decl, Some((nd, name))) {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "port net `{}` declared multiple times",
                                name.name
                            ))
                            .span(name.name_span)
                            .add_note("previous declaration was here:")
                            .span(prev.1.name_span),
                        );
                    }
                }
            }
            _ => continue,
        }
    }

    // As a third step, merge the port declarations with the optional variable
    // and net declarations.
    for port in &mut decl_order {
        // Check if the port is already complete, that is, already has a net or
        // variable type. In that case it's an error to provide an additional
        // variable or net declaration that goes with it.
        if port.kind.is_some() || port.ty.data != ast::ImplicitType {
            for span in port
                .var_decl
                .iter()
                .map(|x| x.1.span)
                .chain(port.net_decl.iter().map(|x| x.1.span))
            {
                cx.emit(
                    DiagBuilder2::error(format!(
                        "port `{}` is complete; additional declaration forbidden",
                        port.name
                    ))
                    .span(span)
                    .add_note(
                        "Port already has a net/variable type. Cannot declare an additional \
                         net/variable with the same name.",
                    )
                    .add_note("Port declaration was here:")
                    .span(port.span),
                );
            }
            port.var_decl = None;
            port.net_decl = None;
        }

        // Extract additional details of the port from optional variable and net
        // declarations.
        let (add_span, add_ty, add_sign, add_packed, add_unpacked) =
            match (port.var_decl, port.net_decl) {
                // Inherit details from a variable declaration.
                (Some(vd), None) => {
                    // TODO: Pretty sure that this can never happen, since a port
                    // which already provides this information is considered
                    // complete.
                    if port.kind.is_some() && port.kind != Some(ast::VarKind::Var) {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "net port `{}` redeclared as variable",
                                port.name
                            ))
                            .span(vd.1.span)
                            .add_note("Port declaration was here:")
                            .span(port.span),
                        );
                    }
                    port.kind = Some(ast::VarKind::Var);
                    (
                        vd.1.name_span,
                        &vd.0.ty.kind,
                        vd.0.ty.sign,
                        &vd.0.ty.dims,
                        &vd.1.dims,
                    )
                }
                // Inherit details from a net declaration.
                (None, Some(nd)) => {
                    // TODO: Pretty sure that this can never happen, since a port
                    // which already provides this information is considered
                    // complete.
                    if port.kind.is_some() && port.kind == Some(ast::VarKind::Var) {
                        cx.emit(
                            DiagBuilder2::error(format!(
                                "variable port `{}` redeclared as net",
                                port.name
                            ))
                            .span(nd.1.span)
                            .add_note("Port declaration was here:")
                            .span(port.span),
                        );
                    }
                    port.kind = Some(ast::VarKind::Net {
                        ty: nd.0.net_type,
                        kind: ast::NetKind::None,
                    });
                    (
                        nd.1.name_span,
                        &nd.0.ty.kind,
                        nd.0.ty.sign,
                        &nd.0.ty.dims,
                        &nd.1.dims,
                    )
                }
                // Handle the case where both are present.
                (Some(vd), Some(nd)) => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "port `{}` doubly declared as variable and net",
                            port.name
                        ))
                        .span(vd.1.span)
                        .span(nd.1.span)
                        .add_note("Port declaration was here:")
                        .span(port.span),
                    );
                    continue;
                }
                // Otherwise we keep things as they are.
                (None, None) => continue,
            };

        // Merge the sign.
        match (port.sign, add_sign) {
            (a, b) if a == b => port.sign = a,
            (a, ast::TypeSign::None) => port.sign = a,
            (ast::TypeSign::None, b) => port.sign = b,
            (_, _) => {
                cx.emit(
                    DiagBuilder2::error(format!("port `{}` has contradicting signs", port.name))
                        .span(port.span)
                        .span(add_span),
                );
            }
        }

        // Merge the type.
        port.match_ty = Some((
            match (&port.ty.data, &add_ty.data) {
                (_, ast::ImplicitType) => None,
                (ast::ImplicitType, _) => {
                    port.ty = Cow::Borrowed(add_ty);
                    None
                }
                (_, _) => Some(add_ty),
            },
            add_packed,
            add_unpacked,
        ));
    }

    // As a fourth step, go through the ports themselves and pair them up with
    // declarations inside the node body. This forms the external view of the
    // ports.
    let mut ext_pos: Vec<ExtPort> = vec![];
    let mut ext_named: HashMap<Name, usize> = HashMap::new();
    let mut any_unnamed = false;
    for port in ast_ports {
        let (name, exprs) = match port.data {
            // [direction] "." ident "(" [expr] ")"
            ast::PortData::Explicit {
                dir: None,
                name,
                ref expr,
            } => {
                if let Some(expr) = expr {
                    let pe = lower_port_expr(cx, expr, node.id());
                    (Some(name), pe)
                } else {
                    (Some(name), vec![])
                }
            }

            // [direction] [net_type|"var"] type_or_implicit ident {dimension} ["=" expr]
            ast::PortData::Named {
                dir: None,
                kind: None,
                ty:
                    ast::Type {
                        data:
                            ast::TypeData {
                                kind:
                                    ast::TypeKind {
                                        data: ast::ImplicitType,
                                        ..
                                    },
                                sign: ast::TypeSign::None,
                                dims: ref packed_dims,
                                ..
                            },
                        ..
                    },
                name,
                ref dims,
                expr: None,
            } if packed_dims.is_empty() => {
                // Now we have to deal with the problem that a port like
                // `foo[7:0]` is interpreted as a named type by the parser, but
                // is actually an implicit port. This is indicated by the dims
                // of the port being non-empty. In this case we recast the dims
                // as selects in a port expression.
                let selects = dims
                    .iter()
                    .map(|dim| match dim {
                        ast::TypeDim::Expr(index) => ExtPortSelect::Index(hir::IndexMode::One(
                            cx.map_ast_with_parent(AstNode::Expr(index), node.id()),
                        )),
                        ast::TypeDim::Range(lhs, rhs) => {
                            ExtPortSelect::Index(hir::IndexMode::Many(
                                ast::RangeMode::Absolute,
                                cx.map_ast_with_parent(AstNode::Expr(lhs), node.id()),
                                cx.map_ast_with_parent(AstNode::Expr(rhs), node.id()),
                            ))
                        }
                        _ => {
                            cx.emit(
                                DiagBuilder2::error(format!(
                                    "invalid port range {}; on port `{}`",
                                    dim.desc_full(),
                                    name
                                ))
                                .span(port.span()),
                            );
                            ExtPortSelect::Error
                        }
                    })
                    .collect();
                let pe = vec![PartialPortExpr { name, selects }];

                // If dims are empty, then this is a named port. Otherwise it's
                // actually an implicit port with no name.
                if dims.is_empty() {
                    (Some(name), pe)
                } else {
                    (None, pe)
                }
            }

            // expr
            ast::PortData::Implicit(ref expr) => (None, lower_port_expr(cx, expr, node.id())),

            // Everything else is just an error.
            _ => {
                cx.emit(
                    DiagBuilder2::error("ANSI port in non-ANSI port list")
                        .span(port.span())
                        .add_note("First port uses non-ANSI style:")
                        .span(first_span),
                );
                error!("Invalid port: {:?}", port);
                continue;
            }
        };
        // trace!("Port {:?}: {:?}", name, exprs);

        // Resolve the port expressions to actual ports in the list.
        let exprs = exprs
            .into_iter()
            .flat_map(|expr| match decl_names.get(&expr.name.value) {
                Some(&index) => Some(ExtPortExpr {
                    port: index,
                    selects: expr.selects,
                }),
                None => {
                    cx.emit(
                        DiagBuilder2::error(format!(
                            "port `{}` not declared in {:#} body",
                            expr.name, node
                        ))
                        .span(expr.name.span)
                        .add_note(format!("Declare the port inside the {:#}, e.g.:", node))
                        .add_note(format!("input {};", expr.name)),
                    );
                    None
                }
            })
            .collect();

        // Wrap things up in an external port.
        let port = ExtPort {
            id: cx.alloc_id(port.span()),
            node,
            span: port.span(),
            name,
            exprs,
        };

        // Build a map of ordered and named port associations.
        if let Some(name) = port.name {
            if ext_named.insert(name.value, ext_pos.len()).is_some() {
                // If the other port maps to the exact same thing, this is
                // admissible, but we lose the ability to perform named
                // connections.
                any_unnamed = true;
            }
        } else {
            any_unnamed = true;
        }
        ext_pos.push(port);
    }

    PartialPortList {
        int: decl_order,
        ext_pos,
        ext_named: if any_unnamed { None } else { Some(ext_named) },
    }
}

/// Lower an AST expression as a port expression.
///
/// ```plain
/// port_expression ::= port_reference | "{" port_reference {"," port_reference} "}"
/// ```
fn lower_port_expr<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &'gcx ast::Expr<'gcx>,
    parent: NodeId,
) -> Vec<PartialPortExpr> {
    match &expr.data {
        ast::ConcatExpr {
            repeat: None,
            exprs,
        } => exprs
            .iter()
            .flat_map(|expr| lower_port_ref(cx, expr, parent))
            .collect(),
        _ => lower_port_ref(cx, expr, parent).into_iter().collect(),
    }
}

/// Lower an AST expression as a port reference.
///
/// ```plain
/// port_reference ::= port_identifier constant_select
/// ```
fn lower_port_ref<'gcx>(
    cx: &impl Context<'gcx>,
    expr: &'gcx ast::Expr<'gcx>,
    parent: NodeId,
) -> Option<PartialPortExpr> {
    match &expr.data {
        ast::IdentExpr(ident) => Some(PartialPortExpr {
            name: *ident,
            selects: vec![],
        }),
        ast::IndexExpr { indexee, index } => {
            let mut pe = lower_port_ref(cx, indexee, parent)?;
            // TODO: This function is really just a tiny snippet. Maybe move
            // this into the RST lowering?
            let mode = crate::hir::lowering::lower_index_mode(cx, index, parent);
            pe.selects.push(ExtPortSelect::Index(mode));
            Some(pe)
        }
        _ => {
            cx.emit(
                DiagBuilder2::error(format!(
                    "invalid port expression: `{}`",
                    expr.span.extract()
                ))
                .span(expr.span),
            );
            error!("{:?}", expr);
            None
        }
    }
}

#[derive(Debug)]
struct PartialPort<'a> {
    span: Span,
    name: Spanned<Name>,
    /// The AST node from which we derived this port.
    ast: &'a dyn ast::AnyNode<'a>,
    dir: ast::PortDir,
    kind: Option<ast::VarKind>,
    sign: ast::TypeSign,
    ty: Cow<'a, ast::TypeKind<'a>>,
    ty_span: Option<Span>,
    packed_dims: &'a [ast::TypeDim<'a>],
    unpacked_dims: &'a [ast::TypeDim<'a>],
    /// The default value assigned to this port if left unconnected.
    default: Option<&'a ast::Expr<'a>>,
    /// Whether the port characteristics are inferred from a declaration in the
    /// node. This is used for explicitly-named ANSI ports.
    inferred: bool,
    /// The variable declaration associated with a non-ANSI port.
    var_decl: Option<(&'a ast::VarDecl<'a>, &'a ast::VarDeclName<'a>)>,
    /// The net declaration associated with a non-ANSI port.
    net_decl: Option<(&'a ast::NetDecl<'a>, &'a ast::VarDeclName<'a>)>,
    /// Redundant type information which must be checked against the non-ANSI
    /// port later.
    match_ty: Option<(
        Option<&'a ast::TypeKind<'a>>,
        &'a [ast::TypeDim<'a>],
        &'a [ast::TypeDim<'a>],
    )>,
}

#[derive(Debug)]
struct PartialPortExpr {
    name: Spanned<Name>,
    selects: Vec<ExtPortSelect>,
}

#[derive(Debug)]
struct PartialPortList<'a> {
    /// The internal ports.
    int: Vec<PartialPort<'a>>,
    /// The external ports, in order for positional connections. Port indices
    /// are indices into `int`.
    ext_pos: Vec<ExtPort<'a>>,
    /// The external ports, for named connections. Values are indices into
    /// `ext_pos`.
    ext_named: Option<HashMap<Name, usize>>,
}
