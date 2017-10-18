// Copyright (c) 2017 Fabian Schuiki

//! This module implements the lowering ports to HIR.

use moore_common::errors::*;
use moore_svlog_syntax::ast;
use nodes::*;
use lower::{Lowerer, is_type_empty, Result};


#[derive(Debug)]
struct PartialPort {
	pub name: Option<Name>,
	pub span: Span,
	pub slices: Vec<PartialPortSlice>,
}

#[derive(Debug)]
struct PartialPortSlice {
	pub id: NodeId,
	pub name: Name,
	pub span: Span,
	pub selects: Vec<PortSelect>,
	pub dir: Option<ast::PortDir>,
	pub kind: Option<ast::PortKind>,
	pub ty: Option<ast::Type>,
	pub dims: Vec<ast::TypeDim>,
}


impl<'a> Lowerer<'a> {
	/// Lower the ports of a module or interface. The function first determines
	/// whether the ports are declared in ANSI or non-ANSI style, then proceeds
	/// to map them to HIR nodes, applying default values for port kind, sign,
	/// and type.
	pub fn map_ports(&mut self, ports: Vec<ast::Port>, items: &[ast::HierarchyItem]) -> Result<Vec<Port>> {
		// Determine whether the first port has type, sign, and direction
		// omitted. If it has, the ports are declared in non-ANSI style.
		let (nonansi, first_span) = {
			let first = match ports.first() {
				Some(p) => p,
				None => return Ok(vec![]),
			};
			let nonansi = match *first {
				ast::Port::Explicit { ref dir, .. } if dir.is_none() => true,
				ast::Port::Named { ref dir, ref kind, ref ty, ref dims, ref expr, .. } if dir.is_none() && kind.is_none() && dims.is_empty() && expr.is_none() && is_type_empty(ty) => true,
				ast::Port::Implicit(_) => true,
				_ => false,
			};
			(nonansi, first.span())
		};

		// Lower the non-ANSI and ANSI ports to a common style.
		let partial_ports = if nonansi {
			self.map_nonansi_ports(ports, items, first_span)
		} else {
			self.map_ansi_ports(ports, items, first_span)
		};
		if self.is_error() {
			return Err(());
		}

		// Apply default sign, port kind, and data type.
		let default_net_type = ast::NetType::Wire;
		let mut mapped_ports = Vec::new();
		for port in partial_ports {
			let mut slices = Vec::new();

			// Finalize the port's partial slices by applying default values for
			// kind, data type, and sign.
			for slice in port.slices {
				let dir = slice.dir.unwrap();
				let mut ty = slice.ty;
				let ty_impl = match ty {
					Some(ref t) => t.data == ast::ImplicitType,
					None => false,
				};

				// Apply a default port kind.
				let kind = if let Some(k) = slice.kind {
					k
				} else {
					match dir {
						ast::PortDir::Input | ast::PortDir::Inout => ast::PortKind::Net(default_net_type),
						ast::PortDir::Output => if ty_impl {
							ast::PortKind::Net(default_net_type)
						} else {
							ast::PortKind::Var
						},
						ast::PortDir::Ref => ast::PortKind::Var,
					}
				};

				// Apply the default data type and sign.
				if let Some(ref mut ty) = ty {
					if ty.data == ast::ImplicitType {
						ty.data = ast::LogicType;
					}
					if ty.sign == ast::TypeSign::None {
						ty.sign = ast::TypeSign::Unsigned;
					}
				}

				assert!(slice.id.as_usize() > 0);
				slices.push(PortSlice {
					id: slice.id,
					name: slice.name,
					span: slice.span,
					selects: slice.selects,
					dir: dir,
					kind: kind,
					ty: ty,
					dims: slice.dims,
				});
			}

			// Create the final port from the partial one.
			mapped_ports.push(Port {
				name: port.name,
				span: port.span,
				slices: slices,
			});
		}


		// Verify that `inout` ports are of net kind, and `ref` ports are of var
		// kind.
		for port in &mapped_ports {
			for slice in &port.slices {
				match (slice.dir, slice.kind) {
					(ast::PortDir::Inout, ast::PortKind::Var) => self.add_diag(
						DiagBuilder2::error(format!("port {} has direction inout but is a variable; needs to be a net port", slice.name))
						.span(slice.span)
					),
					(ast::PortDir::Ref, ast::PortKind::Net(nt)) => self.add_diag(
						DiagBuilder2::error(format!("port {} has direction `ref` but is a net port; needs to be a variable", slice.name))
						.span(slice.span)
					),
					_ => ()
				}
			}
		}
		if self.is_error() {
			return Err(());
		}

		Ok(mapped_ports)
	}


	/// Lower a list of ports, assuming they are presented in ANSI-style.
	fn map_ansi_ports(&mut self, ports: Vec<ast::Port>, items: &[ast::HierarchyItem], first_span: Span) -> Vec<PartialPort> {
		// Since for ANSI-style ports all the information is in the header,
		// ensure that there are no port declarations among the items.
		for item in items {
			match *item {
				ast::HierarchyItem::PortDecl(ref decl) => {
					self.add_diag(DiagBuilder2::error("port declarations are only allowed if a non-ANSI port list is used")
						.span(decl.span));
					self.add_diag(DiagBuilder2::note(format!("...but first port uses ANSI style"))
						.span(first_span)
						.add_note("non-ANSI ports cannot have a direction, type, or kind"));
					break;
				}
				_ => ()
			}
		}


		// Map each of the ports to a HIR port node. Note that each port only
		// has one slice and not selects, as these are only supported in
		// non-ANSI port style.
		let default_ty = ast::Type {
			span: first_span.begin().into(),
			data: ast::LogicType,
			sign: ast::TypeSign::None,
			dims: Vec::new(),
		};
		let mut carry_dir = ast::PortDir::Inout;
		let mut carry_kind = None;
		let mut carry_ty = default_ty.clone();

		let mut mapped = Vec::new();
		for port in ports {
			let mut mapped_port = match port {
				// "interface" ["." ident] ident {dimension} ["=" expr]
				ast::Port::Intf{ .. } => {
					unimplemented!();
				}

				// [direction] "." ident "(" [expr] ")"
				ast::Port::Explicit{ span: _, dir, name, expr } => {
					// If no direction has been provided, use the one carried
					// over from the previous port.
					let dir = dir.unwrap_or(carry_dir);

					// FIXME: We just assume that explicitly named ports do not
					// have a port kind. This is likely to be wrong, and the
					// port kind is inherited along with the port type from the
					// expression provided.
					let kind = None;

					// The port type needs to be inferred from the expression at
					// a later stage, so for now we just set the type to None.
					let ty = None;

					// Keep the direction, kind, and type around for the next
					// port in the list, which might want to inherit them.
					carry_dir  = dir;
					carry_kind = kind;
					carry_ty   = default_ty.clone(); // fall back to `logic`

					// TODO: The expression of the port needs to be stored
					// somewhere. Maybe in the same location as the wire/var
					// declaration would go for non-ANSI ports?
					// TODO: Store the direction.
					PartialPort {
						name: Some(name.name),
						span: name.span,
						slices: vec![
							PartialPortSlice {
								id: name.id,
								name: name.name,
								span: name.span,
								selects: Vec::new(),
								dir: Some(dir),
								kind: kind,
								ty: ty,
								dims: Vec::new(),
							}
						],
					}
				}

				// [direction] [net_type|"var"] type_or_implicit ident {dimension} ["=" expr]
				ast::Port::Named{ span: _, dir, kind, ty, name, dims, expr } => {
					// If no direction has been provided, use the one carried
					// over from the previous port.
					let dir = dir.unwrap_or(carry_dir);

					// If no port kind has been provided, use the one carried
					// over from the previous port.
					let kind = kind.or(carry_kind);

					// If no port type has been provided, use the one carried
					// over from the previous port.
					let ty = if is_type_empty(&ty) {
						carry_ty
					} else {
						ty
					};

					// Keep the direction, kind, and type around for the next
					// port in the list, which might want to inherit them.
					carry_dir  = dir;
					carry_kind = kind;
					carry_ty   = ty.clone();

					PartialPort {
						name: Some(name.name),
						span: name.span,
						slices: vec![
							PartialPortSlice {
								id: name.id,
								name: name.name,
								span: name.span,
								selects: Vec::new(),
								dir: Some(dir),
								kind: kind,
								ty: Some(ty),
								dims: dims,
							}
						],
					}
				}

				// expr
				ast::Port::Implicit(expr) => {
					self.add_diag(DiagBuilder2::error("non-ANSI port in ANSI port list").span(expr.span));
					continue;
				}
			};

			// If the port kind has been omitted, derive it from the direction
			// and type of the port.
			{
				let mut slice = &mut mapped_port.slices[0];
				if slice.kind.is_none() {
					// FIXME: The following can be adjusted through a compiler
					// directive.
					let default_net_type = ast::NetType::Wire;
					match (slice.dir.unwrap(), &slice.ty) {
						(ast::PortDir::Input, _) |
						(ast::PortDir::Inout, _) => {
							slice.kind = Some(ast::PortKind::Net(default_net_type));
						}
						(ast::PortDir::Output, &Some(ref ty)) => {
							if ty.data == ast::ImplicitType {
								slice.kind = Some(ast::PortKind::Net(default_net_type));
							} else {
								slice.kind = Some(ast::PortKind::Var);
							}
						}
						(ast::PortDir::Ref, _) => {
							slice.kind = Some(ast::PortKind::Var);
						}
						_ => ()
					}
				}
			}

			mapped.push(mapped_port);
		}

		mapped
	}


	/// Lower a list of ports, assuming they are presented in non-ANSI-style.
	fn map_nonansi_ports(&mut self, ports: Vec<ast::Port>, items: &[ast::HierarchyItem], first_span: Span) -> Vec<PartialPort> {
		let mut mapped = Vec::new();

		// Create a stub port for each port in the list. Port declarations in
		// the body of the module/interface will later on further specify the
		// details of the port.
		//
		// A port has a name which can be used when instantiating the module,
		// and an expression describing what internal variable/net the port
		// connects to. The name can either be given explicitly, e.g. the `foo`
		// in `.foo(bar)`, or implicitly as in `baz`. However, ports that are
		// a concatenation or part-select, e.g. `{a,b}` or `a[3:0]` have no such
		// name.
		for port in ports {
			let (span, name, expr): (Span, Option<ast::Identifier>, Option<ast::Expr>) = match port {
				// "interface" ["." ident] ident {dimension} ["=" expr]
				ast::Port::Intf{ span, .. } => {
					self.add_diag(DiagBuilder2::error("interface ports are only allowed in an ANSI port list")
						.span(span));
					self.add_diag(DiagBuilder2::note("...but first port uses non-ANSI style")
						.span(first_span));
					return Vec::new();
				}

				// [direction] "." ident "(" [expr] ")"
				ast::Port::Explicit{ span, dir, name, expr } => {
					if dir.is_some() {
						self.add_diag(DiagBuilder2::error("port directions are only allowed in an ANSI port list")
							.span(span));
						self.add_diag(DiagBuilder2::note("...but first port uses non-ANSI style")
							.span(first_span));
					}
					(span, Some(name), expr)
				}

				// [direction] [net_type|"var"] type_or_implicit ident {dimension} ["=" expr]
				ast::Port::Named{ span, dir, kind, ty, name, dims, expr } => {
					if dir.is_some() || kind.is_some() || !is_type_empty(&ty) || expr.is_some() {
						self.add_diag(DiagBuilder2::error("ANSI style port in a non-ANSI style port list")
							.span(span));
					}

					// Convert the name of the port into an expression. This
					// will then be used as the expression of the port stub.
					let mut expr = ast::Expr {
						span: span,
						data: ast::IdentExpr(ast::Identifier {
							id: name.id,
							name: name.name,
							span: name.span,
						}),
					};

					// If there are additional dimensions specified, this
					// actually is a part-select of something defined within a
					// module.
					if !dims.is_empty() {
						// for example: `a[3:0]`
						panic!("the part-select of port {} has not been converted into an expression properly", name.name);
						// (span, None, Some(expr))
					} else {
						// for example: `a`
						(span, Some(name), Some(expr))
					}
				}

				// expr
				ast::Port::Implicit(expr) => {
					(expr.span, None, Some(expr))
				}
			};


			// Now we have an optional name of the port, and an optional
			// expression for the port. The latter can only be a concatenation
			// or part-select of a port declaration within the module. So we now
			// need to disassemble the expression step-by-step and map it to the
			// Port/PortSlice/PortSelect structure used in the HIR.
			let mut slices = Vec::new();
			match expr {
				Some(ast::Expr { data: ast::ConcatExpr { repeat, exprs }, ..}) => {
					if let Some(repeat) = repeat {
						self.add_diag(DiagBuilder2::error("concatenation in port list cannot have a repeat count")
							.span(repeat.span));
					}
					for expr in exprs {
						match self.map_nonansi_port_expr(expr) {
							Ok(ps) => slices.push(ps),
							Err(()) => (),
						}
					}
				},
				Some(e) => match self.map_nonansi_port_expr(e) {
					Ok(ps) => slices.push(ps),
					Err(()) => (),
				},
				None => ()
			}

			// TODO: Find the port declarations and optional wire/var
			// declarations that go with each of the slices. Create wire/var
			// declarations as appropriate if only the port declaration is
			// provided.
			for slice in &mut slices {
				let (port_decls, var_decls, net_decls) = self.find_items_relevant_to_port(items, slice.name);

				// Ensure that there is at most one port, variable, and net
				// declaration associated with the port, and extract those.
				fn ensure_one_or_none<T, Fa, Fb>(l: &mut Lowerer, decls: Vec<T>, to_name: Fa, to_span: Fb) -> Option<T>
					where Fa: Fn(&T) -> Name, Fb: Fn(&T) -> Span {
					let mut iter = decls.into_iter();
					let first = iter.next();
					for other in iter {
						let first = first.as_ref().unwrap();
						l.add_diag(
							DiagBuilder2::error(format!("`{}` declared multiple times", to_name(&other)))
							.span(to_span(&other))
						);
						l.add_diag(
							DiagBuilder2::note(format!("previous declaration of `{}` was here", to_name(first)))
							.span(to_span(first))
						);
					}
					first
				}

				let port_decl = match ensure_one_or_none(self, port_decls, |x| (x.1).name, |x| (x.1).span) {
					Some(x) => x,
					None => {
						self.add_diag(
							DiagBuilder2::error(format!("missing port declaration for `{}`", slice.name))
							.span(slice.span)
							.add_note("non-ANSI ports need a port declaration inside the module")
						);
						continue;
					}
				};
				let mut var_decl  = ensure_one_or_none(self, var_decls,  |x| (x.1).name, |x| (x.1).span);
				let mut net_decl  = ensure_one_or_none(self, net_decls,  |x| (x.1).name, |x| (x.1).span);


				// Determine whether the port declaration is complete, which is
				// the case if it contains a net or variable type. Complete
				// ports cannot have a var or net declaration associated with
				// them.
				let complete = port_decl.0.net_type.is_some() || port_decl.0.ty.data != ast::ImplicitType;
				if complete {
					for span in var_decl.iter().map(|x| x.1.span).chain(net_decl.iter().map(|x| x.1.span)) {
						self.add_diag(
							DiagBuilder2::error(format!("port `{}` is completely declared; cannot provide an additional variable/net declaration", slice.name))
							.span(span)
						);
					}
					var_decl = None;
					net_decl = None;
				}


				// Based on the information provided in the port declaration,
				// see if we can already determine whether this will be a var
				// or net port.
				let mut kind = if port_decl.0.var {
					Some(ast::PortKind::Var)
				} else if let Some(nt) = port_decl.0.net_type {
					Some(ast::PortKind::Net(nt))
				} else {
					None
				};


				// Analyze the var or net declaration to determine the rest of
				// the port information.
				let (final_ty, final_dims) =
				if let Some((data_ty, data_dims, span)) = match (var_decl, net_decl) {
					// Port + variable declaration
					(Some(var), None) if !complete => {
						if let Some(ast::PortKind::Net(_)) = kind {
							self.add_diag(DiagBuilder2::error(format!("`{}` is a net port, but it is also declared as a variable", slice.name)).span(var.1.span));
							continue;
						}
						kind = Some(ast::PortKind::Var);
						Some((&var.0.ty, &var.1.dims, var.1.span))
					}

					// Port + net declaration
					(None, Some(net)) if !complete => {
						if let Some(ast::PortKind::Var) = kind {
							self.add_diag(DiagBuilder2::error(format!("`{}` is a variable port, but it is also declared as a net", slice.name)).span(net.1.span));
							continue;
						}
						kind = Some(ast::PortKind::Net(net.0.net_type));
						Some((&net.0.ty, &net.1.dims, net.1.span))
					}

					// Port + variable + net declaration (error)
					(Some(var), Some(net)) if !complete => {
						self.add_diag(DiagBuilder2::error(format!("conflicting variable and net declarations for port `{}`", slice.name)).span(var.1.span).span(net.1.span));
						continue;
					}

					_ => None
				} {
					// Determine the sign of the type.
					let res_sign = match (port_decl.0.ty.sign, data_ty.sign) {
						(a, b) if a == b => a,
						(a, ast::TypeSign::None) => a,
						(ast::TypeSign::None, b) => b,
						(a, b) if a != b => {
							// TODO: Actually highlight the span of the sign,
							// rather than the name of the port.
							// TODO: Have the TypeSign implement fmt::Display.
							self.add_diag(
								DiagBuilder2::error(format!("port `{}` has contradicting sign", slice.name))
								.add_note(format!("port declaration says {:?}", a))
								.span(port_decl.1.span)
								.add_note(format!("variable/net declaration says {:?}", b))
								.span(span)
							);
							continue;
						}
						_ => unreachable!()
					};


					// Determine the actual type data itself.
					let (res_data, res_span) = match (&port_decl.0.ty.data, &data_ty.data) {
						(a, b) if a == b => (&port_decl.0.ty.data, port_decl.0.ty.span),
						(a, &ast::ImplicitType) => (&port_decl.0.ty.data, port_decl.0.ty.span),
						(&ast::ImplicitType, b) => (&data_ty.data, data_ty.span),
						_ => unreachable!()
					};


					// TODO: Ensure the type dimensions match. This might only
					// become possible at a later stage when we can resolve
					// constant expressions.
					let res_dims = &port_decl.0.ty.dims;


					// TODO: Ensure the data dimensions match. This might only
					// become possible at a later stage when we can resolve
					// constant expressions.
					let res_data_dims = &port_decl.1.dims;


					// Assemble the above information into a type that we can
					// assign to the slice.
					(
						ast::Type {
							span: res_span,
							data: res_data.clone(),
							sign: res_sign,
							dims: res_dims.clone(),
						},
						res_data_dims
					)
				} else {
					(
						port_decl.0.ty.clone(),
						&port_decl.1.dims
					)
				};

				// Store the derived information in the slice.
				slice.dir = Some(port_decl.0.dir);
				slice.kind = kind;
				slice.ty = Some(final_ty);
				slice.dims = final_dims.clone();
			}

			// Wrap things up in a port.
			mapped.push(PartialPort {
				name: name.map(|ident| ident.name),
				span: span,
				slices: slices,
			});
		}

		mapped
	}


	fn map_nonansi_port_expr(&mut self, mut expr: ast::Expr) -> Result<PartialPortSlice> {
		let mut selects = Vec::new();
		loop {
			match expr.data {
				ast::IdentExpr(ident) => {
					selects.reverse();
					return Ok(PartialPortSlice {
						id: ident.id,
						name: ident.name,
						span: ident.span,
						selects: selects,
						dir: None,
						kind: None,
						ty: None,
						dims: Vec::new(),
					});
				},
				ast::IndexExpr { indexee, index } => {
					selects.push(PortSelect::Index(index.span, Expr{}));
					expr = *indexee;
				},
				ast::MemberExpr { expr: e, name } => {
					selects.push(PortSelect::Member(name.span, name.name));
					expr = *e;
				}
				_ => {
					self.add_diag(DiagBuilder2::error("port expression can only contain identifiers, member accesses, index accesses, and concatenations").span(expr.span));
					return Err(());
				}
			}
		}
	}


	/// Find the port, variable, and net declarations with a given name among
	/// a list of hierarchy items. Used during port lowering to gather the
	/// declarations associated with a port.
	fn find_items_relevant_to_port<'b>(&mut self, items: &'b [ast::HierarchyItem], name: Name) -> (
		Vec<(&'b ast::PortDecl, &'b ast::VarDeclName)>,
		Vec<(&'b ast::VarDecl,  &'b ast::VarDeclName)>,
		Vec<(&'b ast::NetDecl,  &'b ast::VarDeclName)>,
	) {
		let mut pds = Vec::new();
		let mut vds = Vec::new();
		let mut nds = Vec::new();
		for item in items {
			match *item {
				ast::HierarchyItem::PortDecl(ref pd) => for decl in &pd.names {
					if decl.name == name {
						pds.push((pd, decl));
					}
				},
				ast::HierarchyItem::VarDecl(ref vd) => for decl in &vd.names {
					if decl.name == name {
						vds.push((vd, decl));
					}
				},
				ast::HierarchyItem::NetDecl(ref nd) => for decl in &nd.names {
					if decl.name == name {
						nds.push((nd, decl));
					}
				},
				_ => ()
			}
		}
		(pds, vds, nds)
	}
}
