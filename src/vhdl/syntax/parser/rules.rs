// Copyright (c) 2017 Fabian Schuiki

//! This module implements a first stage recursive descent parser for VHDL. It
//! can process a stream of input tokens into the coarse, generalized abstract
//! syntax tree defined in [`ast`]. The grammar productions/rules outlined in
//! the VHDL standard are collapsed into more general rules as outlined in the
//! following table.
//!
//! | VHDL Standard                        | Generalized to       |
//! |--------------------------------------|----------------------|
//! | aggregate                            | paren_expr           |
//! | array_constraint                     | name                 |
//! | attribute_declaration                | attr_decl            |
//! | attribute_name                       | name                 |
//! | attribute_specification              | attr_decl            |
//! | block_specification                  | name                 |
//! | configuration_item                   | decl_item            |
//! | constraint                           | primary_expr         |
//! | enumeration_type_definition          | paren_expr           |
//! | external_name                        | *ignored*            |
//! | function_call                        | name                 |
//! | generate_specification               | expr                 |
//! | generic_clause                       | generic_clause       |
//! | generic_map_aspect                   | map_aspect           |
//! | group_declaration                    | group_decl           |
//! | group_template_declaration           | group_decl           |
//! | indexed_name                         | name                 |
//! | interface_subprogram_declaration     | subprog_spec         |
//! | name                                 | name                 |
//! | name/character_literal               | primary_name         |
//! | name/operator_symbol                 | primary_name         |
//! | name/simple_name                     | primary_name         |
//! | port_clause                          | port_clause          |
//! | port_map_aspect                      | map_aspect           |
//! | range_constraint                     | name                 |
//! | record_constraint                    | name, paren_expr     |
//! | resolution_indication                | primary_expr         |
//! | selected_name                        | name                 |
//! | slice_name                           | name                 |
//! | subprogram_body                      | subprog_spec         |
//! | subprogram_declaration               | subprog_spec         |
//! | subprogram_instantiation_declaration | subprog_spec         |
//! | subtype_indication                   | name, primary_expr   |
//! | target                               | primary_expr         |
//! | time_expression                      | expr                 |
//! | type_mark                            | name                 |

use std::fmt::Display;
use moore_common::errors::*;
use moore_common::name::*;
use moore_common::source::*;
use lexer::token::*;
use parser::TokenStream;
use parser::core::*;
use ast;

pub trait Parser: TokenStream<Token> {}
impl<T> Parser for T where T: TokenStream<Token> {}

#[derive(Debug)]
pub struct Recovered;
#[derive(Debug)]
pub struct Reported;

pub type RecoveredResult<T> = Result<T, Recovered>;
pub type ReportedResult<T> = Result<T, Reported>;

impl From<Recovered> for Reported {
	fn from(_: Recovered) -> Reported {
		Reported
	}
}

macro_rules! unimp {
    ($parser:expr, $name:expr) => {{
    	let q = $parser.peek(0).span;
    	$parser.emit(
    		DiagBuilder2::error(format!("{} not yet implemented", $name))
    		.span(q)
    	);
    	return Err(Reported);
    }}
}


/// Parse an entire design file. IEEE 1076-2008 section 13.1.
///
/// ```text
/// design_file := {design_unit}+
/// ```
pub fn parse_design_file<P: Parser>(p: &mut P) -> Vec<ast::DesignUnit> {
	let mut units = Vec::new();
	while !p.is_fatal() && p.peek(0).value != Eof {
		match parse_design_unit(p) {
			Ok(unit) => units.push(unit),
			Err(Recovered) => ()
		}
	}
	units
}


/// Parse a single design unit. IEEE 1076-2008 section 13.1.
///
/// ```text
/// design_unit := {context_item} library_unit
/// library_unit
///   := entity_decl
///   := config_decl
///   := package_decl
///   := package_inst_decl
///   := context_decl
///   := arch_body
///   := package_body
/// ```
pub fn parse_design_unit<P: Parser>(p: &mut P) -> RecoveredResult<ast::DesignUnit> {
	let context = repeat(p, try_context_item)?;
	let Spanned{ value: tkn, span: sp } = p.peek(0);
	match match tkn {
		Keyword(Kw::Entity) => parse_entity_decl(p).map(|d| ast::DesignUnitData::EntityDecl(d)),
		Keyword(Kw::Configuration) => parse_config_decl(p).map(|d| ast::DesignUnitData::CfgDecl(d)),
		Keyword(Kw::Package) => {
			if p.peek(1).value == Keyword(Kw::Body) {
				parse_package_body(p).map(|d| ast::DesignUnitData::PkgBody(d))
			} else {
				parse_package_decl(p).map(|d| ast::DesignUnitData::PkgDecl(d))
			}
		}
		Keyword(Kw::Context) => parse_context_decl(p).map(|d| ast::DesignUnitData::CtxDecl(d)),
		Keyword(Kw::Architecture) => parse_arch_body(p).map(|d| ast::DesignUnitData::ArchBody(d)),
		tkn => {
			p.emit(
				DiagBuilder2::error(format!("Expected a primary or secondary unit, instead found {}", tkn))
				.span(sp)
				.add_note("`entity`, `configuration`, `package`, and `context` are primary units")
				.add_note("`architecture` and `package body` are secondary units")
			);
			Err(Reported)
		}
	} {
		Ok(x) => Ok(ast::DesignUnit{
			id: Default::default(),
			ctx: context,
			data: x,
		}),
		Err(Reported) => {
			recover(p, &[Keyword(Kw::End)], true);
			recover(p, &[Semicolon], true);
			recover(p, &[Keyword(Kw::Entity), Keyword(Kw::Configuration), Keyword(Kw::Package), Keyword(Kw::Context), Keyword(Kw::Architecture)], false);
			Err(Recovered)
		}
	}
}


/// Parse a context item. IEEE 1076-2008 section 13.4.
///
/// ```text
/// context_item := library_clause | use_clause | context_ref
/// ```
pub fn try_context_item<P: Parser>(p: &mut P) -> RecoveredResult<Option<ast::CtxItem>> {
	recovered(p, &[Semicolon], true, |p|{
		let tkn = p.peek(0).value;
		Ok(match tkn {
			Keyword(Kw::Library) => Some(ast::CtxItem::LibClause(parse_library_clause(p)?)),
			Keyword(Kw::Use) => Some(ast::CtxItem::UseClause(parse_use_clause(p)?)),
			Keyword(Kw::Context) => {
				if p.peek(2).value != Keyword(Kw::Is) {
					Some(ast::CtxItem::CtxRef(parse_context_ref(p)?))
				} else {
					None
				}
			}
			_ => None
		})
	})
}


/// Parse a library clause. IEEE 1076-2008 section 13.2.
///
/// ```text
/// library_clause := "library" {ident}","+
/// ```
pub fn parse_library_clause<P: Parser>(p: &mut P) -> ReportedResult<Spanned<Vec<ast::Ident>>> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Library))?;
	let names = separated_nonempty(p, Comma, Semicolon, "library name", |p| parse_ident(p, "library name"))?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(Spanned::new(
		names.into_iter().map(|n| ast::Ident::from(n)).collect(),
		span,
	))
}


/// Parse a use clause. IEEE 1076-2008 section 12.4.
///
/// ```text
/// use_clause := "use" {name}","+
/// ```
pub fn parse_use_clause<P: Parser>(p: &mut P) -> ReportedResult<Spanned<Vec<ast::CompoundName>>> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Use))?;
	let names = separated_nonempty(p, Comma, Semicolon, "selected name", parse_name)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(Spanned::new(names, span))
}


pub fn parse_context_ref<P: Parser>(p: &mut P) -> ReportedResult<Spanned<Vec<ast::CompoundName>>> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Context))?;
	let names = separated_nonempty(p, Comma, Semicolon, "selected name", parse_name)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(Spanned::new(names, span))
}


/// Parse a name. IEEE 1076-2008 section 8.
pub fn parse_name<P: Parser>(p: &mut P) -> ReportedResult<ast::CompoundName> {
	let q = p.peek(0).span;
	match try_name(p)? {
		Some(n) => Ok(n),
		None => {
			p.emit(
				DiagBuilder2::error("Expected a name")
				.span(q.begin())
			);
			Err(Reported)
		}
	}
}


/// Try to parse a name. IEEE 1076-2008 section 8.
pub fn try_name<P: Parser>(p: &mut P) -> ReportedResult<Option<ast::CompoundName>> {
	// Parse a primary name.
	let primary = match try_primary_name(p) {
		Some(pn) => pn,
		None => return Ok(None)
	};

	// Wrap it up in a compound name, to be extended with suffices.
	let name = ast::CompoundName{
		id: Default::default(),
		span: primary.span,
		primary: primary,
		parts: Vec::new(),
	};

	// Parse a potential name suffix.
	parse_name_suffix(p, name).map(|x| Some(x))
}


/// Try to parse a primary name. IEEE 1076-2008 section 8.
///
/// ```text
/// primary_name := ident | char_lit | string_lit
/// ```
pub fn try_primary_name<P: Parser>(p: &mut P) -> Option<ast::PrimaryName> {
	let Spanned{ value: tkn, span } = p.peek(0);
	let kind = match tkn {
		Ident(n) => ast::PrimaryNameKind::Ident(n),
		Lit(Literal::Char(c)) => ast::PrimaryNameKind::Char(c),
		Lit(Literal::String(s)) => ast::PrimaryNameKind::String(s),
		_ => return None
	};
	p.bump();
	return Some(ast::PrimaryName{
		id: Default::default(),
		span: span,
		kind: kind,
	});
}


/// Parse the suffix to a name. IEEE 1076-2008 section 8.
///
/// ```text
/// name
///   := primary_name
///   := name "." (ident | char_lit | string_lit | "all")
///   := name [signature] "'" ident
///   := name paren_expr
/// ```
pub fn parse_name_suffix<P: Parser>(p: &mut P, mut name: ast::CompoundName) -> ReportedResult<ast::CompoundName> {
	// Try to parse a selected name.
	if accept(p, Period) {
		// Parse the suffix, which is a primary name or the keyword `all`.
		let suffix = {
			if let Some(pn) = try_primary_name(p) {
				ast::NamePart::Select(pn)
			} else { // `else if accept(...)` breaks on rust 1.15: p borrowed mutably in pattern guard
				if accept(p, Keyword(Kw::All)) {
					ast::NamePart::SelectAll(p.last_span())
				} else {
					let Spanned{ value: wrong, span } = p.peek(0);
					p.emit(
						DiagBuilder2::error("Expected identifier, character literal, operator symbol, or `all` after `.`")
						.span(span)
						.add_note("see IEEE 1076-2008 section 8.3")
					);
					return Err(Reported);
				}
			}
		};

		// Extend the name
		name.span.expand(p.last_span());
		name.parts.push(suffix);
		return parse_name_suffix(p, name);
	}

	// Try to parse a signature.
	if let Some(sig) = try_flanked(p, Brack, parse_signature)? {
		name.span.expand(p.last_span());
		name.parts.push(ast::NamePart::Signature(sig));
		return parse_name_suffix(p, name);
	}

	// Try to parse an attribute name.
	if p.peek(0).value == Apostrophe && p.peek(1).value != OpenDelim(Paren) {
		require(p, Apostrophe)?;

		// Unfortunately `range` is a valid attribute name, even though it is
		// defined as a language keyword. The solution here is quite hacky, but
		// works: We generate a "range" name on the fly and return it as
		// attribute name. The downside is that we lose the capitalization that
		// was present in the source text, which might confuse the user.
		let attr = if accept(p, Keyword(Kw::Range)) {
			Spanned::new(get_name_table().intern("range", false), p.last_span())
		} else {
			parse_ident(p, "attribute name")?
		};

		name.span.expand(p.last_span());
		name.parts.push(ast::NamePart::Attribute(attr.into()));
		return parse_name_suffix(p, name);
	}

	// Try to parse a function call, slice name, or indexed name.
	if let Some(al) = try_paren_expr(p)? {
		name.span.expand(p.last_span());
		name.parts.push(ast::NamePart::Call(al));
		return parse_name_suffix(p, name);
	}

	// Try to parse a range constraint.
	if accept(p, Keyword(Kw::Range)) {
		let expr = parse_expr_prec(p, ExprPrec::Range)?;
		name.parts.push(ast::NamePart::Range(Box::new(expr)));
		name.span.expand(p.last_span());
		return parse_name_suffix(p, name);
	}

	// If we arrive here, none of the suffices matched, and we simply return the
	// prefix that we have received.
	Ok(name)
}


/// Parse the optional trailing name after an entity, configuration, etc., which
/// must match the name at the beginning of the declaration.
fn parse_optional_matching_ident<P,M1,M2,T>(p: &mut P, name: T, msg: M1, sec: M2)
where P: Parser, M1: Display, M2: Display, T: Into<Option<Spanned<Name>>> {
	if let Some(n) = try_ident(p) {
		if let Some(name) = name.into() {
			if n.value != name.value {
				p.emit(
					DiagBuilder2::warning(format!("`{}` does not match {} name `{}`", n.value, msg, name.value))
					.span(n.span)
					.add_note(format!("see IEEE 1076-2008 {}", sec))
				);
			}
		} else {
			p.emit(
				DiagBuilder2::warning(format!("Label `{}` is given at the end of {}, but not at the beginning", n.value, msg))
				.span(n.span)
				.add_note(format!("see IEEE 1076-2008 {}", sec))
			);
		}
	}
}


/// Parse a context declaration. IEEE 1076-2008 section 13.3.
///
/// ```text
/// context_decl :=
///   "context" ident "is"
///     {context_item}
///   "end" ["context"] [ident] ";"
/// ```
pub fn parse_context_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::CtxDecl> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Context))?;
	let name = parse_ident(p, "context name")?;
	require(p, Keyword(Kw::Is))?;
	let items = repeat(p, try_context_item)?;
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Context));
	parse_optional_matching_ident(p, name, "context", "section 13.3");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::CtxDecl{
		id: Default::default(),
		span: span,
		name: name,
		items: items,
	})
}


/// Parse an entity declaration. See IEEE 1076-2008 section 3.2.
///
/// ```text
/// entity_decl :=
///   "entity" ident "is"
///     entity_header
///     entity_decl_part
///   ["begin" {stmt}]
///   "end" ["entity"] [ident] ";"
/// ```
pub fn parse_entity_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::EntityDecl> {
	let mut span = p.peek(0).span;

	// Parse the head of the declaration.
	require(p, Keyword(Kw::Entity))?;
	let name = parse_ident(p, "entity name")?;
	require(p, Keyword(Kw::Is))?;

	// Parse the declarative part.
	let decl_items = repeat(p, try_decl_item)?;

	// Parse the optional statement part.
	let stmts = if accept(p, Keyword(Kw::Begin)) {
		Some(repeat_until(p, Keyword(Kw::End), parse_stmt)?)
	} else {
		None
	};

	// Parse the tail of the declaration.
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Entity));
	parse_optional_matching_ident(p, name, "entity", "section 3.2.1");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::EntityDecl{
		id: Default::default(),
		span: span,
		name: name,
		decls: decl_items,
		stmts: stmts,
	})
}


/// Parse a configuration declaration. See IEEE 1076-2008 section 3.4.
///
/// ```text
/// config_decl :=
///   "configuration" ident "of" name "is"
///     {config_decl_item}
///   "end" ["configuration"] [ident] ";"
/// ```
pub fn parse_config_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::CfgDecl> {
	let mut span = p.peek(0).span;

	// Parse the head of the declaration.
	require(p, Keyword(Kw::Configuration))?;
	let name = parse_ident(p, "configuration name")?;
	require(p, Keyword(Kw::Of))?;
	let target = parse_name(p)?;
	require(p, Keyword(Kw::Is))?;

	// Parse the configuration declarative items.
	let decl_items = repeat_until(p, Keyword(Kw::End), parse_block_comp_decl_item)?;

	// Parse the tail of the declaration.
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Configuration));
	parse_optional_matching_ident(p, name, "configuration", "section 3.4");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::CfgDecl{
		id: Default::default(),
		span: span,
		name: name,
		target: target,
		decls: decl_items,
	})
}


/// Parse an architecture body. See IEEE 1076-2008 section 3.3.
///
/// ```text
/// arch_body :=
///   "architecture" ident "of" name "is"
///     {decl_item}
///   "begin"
///     {stmt}
///   "end" ["architecture"] [ident] ";"
/// ```
pub fn parse_arch_body<P: Parser>(p: &mut P) -> ReportedResult<ast::ArchBody> {
	let mut span = p.peek(0).span;

	// Parse the head of the body.
	require(p, Keyword(Kw::Architecture))?;
	let name = parse_ident(p, "architecture name")?;
	require(p, Keyword(Kw::Of))?;
	let target = parse_name(p)?;
	require(p, Keyword(Kw::Is))?;

	// Parse the declarative and statement parts.
	let decl_items = repeat(p, try_decl_item)?;
	require(p, Keyword(Kw::Begin))?;
	let stmts = repeat_until(p, Keyword(Kw::End), parse_stmt)?;

	// Parse the tail of the body.
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Architecture));
	parse_optional_matching_ident(p, name, "architecture", "section 3.3");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::ArchBody{
		id: Default::default(),
		span: span,
		name: name,
		target: target,
		decls: decl_items,
		stmts: stmts,
	})
}


/// Try to parse a generic clause. See IEEE 1076-2008 section 6.5.6.2.
///
/// ```text
/// generic_clause := "generic" "clause" "(" {intf_decl}";"+ ")" ";"
/// ```
pub fn try_generic_clause<P: Parser>(p: &mut P) -> ReportedResult<Option<Spanned<Vec<ast::IntfDecl>>>> {
	if p.peek(0).value == Keyword(Kw::Generic) && p.peek(1).value != Keyword(Kw::Map) {
		p.bump();
		let mut span = p.last_span();
		let i = flanked(p, Paren, |p|{
			Ok(separated_nonempty(p,
				Semicolon,
				CloseDelim(Paren),
				"generic interface declaration",
				|p| parse_intf_decl(p, Some(ast::IntfObjKind::Const))
			)?)
		})?;
		require(p, Semicolon)?;
		span.expand(p.last_span());
		Ok(Some(Spanned::new(i, span)))
	} else {
		Ok(None)
	}
}


/// Try to parse a port clause. See IEEE 1076-2008 section 6.5.6.3.
///
/// ```text
/// port_clause := "port" "clause" "(" {intf_decl}";"+ ")" ";"
/// ```
pub fn try_port_clause<P: Parser>(p: &mut P) -> ReportedResult<Option<Spanned<Vec<ast::IntfDecl>>>> {
	if p.peek(0).value == Keyword(Kw::Port) && p.peek(1).value != Keyword(Kw::Map) {
		p.bump();
		let mut span = p.last_span();
		let i = flanked(p, Paren, |p|{
			Ok(separated_nonempty(p,
				Semicolon,
				CloseDelim(Paren),
				"port interface declaration",
				|p| parse_intf_decl(p, Some(ast::IntfObjKind::Signal))
			)?)
		})?;
		require(p, Semicolon)?;
		span.expand(p.last_span());
		Ok(Some(Spanned::new(i, span)))
	} else {
		Ok(None)
	}
}


/// Parse an interface declaration. These are generally part of an interface
/// list as they appear in generic and port clauses within for example entity
/// declarations. See IEEE 1076-2008 section 6.5.1.
pub fn parse_intf_decl<P: Parser>(p: &mut P, default: Option<ast::IntfObjKind>) -> ReportedResult<ast::IntfDecl> {
	let Spanned{ value: tkn, mut span } = p.peek(0);
	let kind = match tkn {
		// Try to short-circuit a type interface declarations.
		Keyword(Kw::Type) => return parse_type_decl(p, false).map(|d| ast::IntfDecl::TypeDecl(d)),

		// Try to short-circuit a subprogram interface declaration.
		Keyword(Kw::Pure) |
		Keyword(Kw::Impure) |
		Keyword(Kw::Procedure) |
		Keyword(Kw::Function) => {
			let spec = parse_subprog_spec(p)?;
			let default = if accept(p, Keyword(Kw::Is)) {
				if accept(p, LtGt) {
					// subprog_spec "is" "<>"
					Some(ast::SubprogDefault::Any)
				} else if let Some(name) = try_name(p)? {
					// subprog_spec "is" name
					Some(ast::SubprogDefault::Name(name))
				} else {
					p.emit(
						DiagBuilder2::error(format!("Expected default subprogram name or `<>` after `is`, found {} instead", tkn))
						.span(span)
						.add_note("see IEEE 1076-2008 section 6.5.4")
					);
					return Err(Reported);
				}
			} else {
				None
			};
			span.expand(p.last_span());
			return Ok(ast::IntfDecl::SubprogSpec(ast::IntfSubprogDecl{
				id: Default::default(),
				span: span,
				spec: spec,
				default: default,
			}));
		}

		// Try to short-circuit a package interface declaration.
		Keyword(Kw::Package) => {
			let inst = parse_package_inst(p, false)?;
			return Ok(ast::IntfDecl::PkgInst(inst));
		}

		// Try to parse one of the object declarations.
		Keyword(Kw::Constant) => { p.bump(); ast::IntfObjKind::Const }
		Keyword(Kw::Signal)   => { p.bump(); ast::IntfObjKind::Signal }
		Keyword(Kw::Variable) => { p.bump(); ast::IntfObjKind::Var }
		Keyword(Kw::File)     => { p.bump(); ast::IntfObjKind::File }
		_ => {
			if let Some(k) = default {
				k
			} else {
				p.emit(
					DiagBuilder2::error("Expected an interface declaration")
					.span(span)
					.add_note("`constant`, `signal`, `variable`, and `file` start an object declaration")
					.add_note("`type` starts a type declaration")
					.add_note("`procedure`, `function`, `pure function`, or `impure function` start a subprogram declaration")
					.add_note("`package` starts a package declaration")
					.add_note("see IEEE 1076-2008 section 6.5")
				);
				return Err(Reported);
			}
		}
	};

	// Parse the object names.
	let names = separated_nonempty(p, Comma, Colon, "object name", |p| parse_ident(p, "object name"))?;
	require(p, Colon)?;

	// Parse the optional mode.
	let mode = match p.peek(0).value {
		Keyword(Kw::In) => { p.bump(); Some(ast::IntfMode::In) },
		Keyword(Kw::Out) => { p.bump(); Some(ast::IntfMode::Out) },
		Keyword(Kw::Inout) => { p.bump(); Some(ast::IntfMode::Inout) },
		Keyword(Kw::Buffer) => { p.bump(); Some(ast::IntfMode::Buffer) },
		Keyword(Kw::Linkage) => { p.bump(); Some(ast::IntfMode::Linkage) },
		_ => None,
	};

	// Parse the type and optional `bus` keyword.
	let ty = parse_subtype_ind(p)?;
	let bus = accept(p, Keyword(Kw::Bus));

	// Parse the optional default expression.
	let def = if accept(p, VarAssign) {
		Some(parse_expr(p)?)
	} else {
		None
	};

	span.expand(p.last_span());
	Ok(ast::IntfDecl::ObjDecl(ast::IntfObjDecl{
		kind: kind,
		span: span,
		names: names.into_iter().map(|n| ast::Ident::from(n)).collect(),
		mode: mode,
		ty: ty,
		bus: bus,
		default: def,
	}))
}


/// Try to parse a declarative item. See IEEE 1076-2008 section 3.2.3.
pub fn try_decl_item<P: Parser>(p: &mut P) -> ReportedResult<Option<ast::DeclItem>> {
	let mut span = p.peek(0).span;
	Ok(match p.peek(0).value {
		// package_decl := "package" ident "is" ...
		// package_body := "package" "body" ident "is" ...
		// package_inst := "package" ident "is" "new" ...
		Keyword(Kw::Package) => {
			if p.peek(1).value == Keyword(Kw::Body) {
				Some(ast::DeclItem::PkgBody(parse_package_body(p)?))
			} else if p.peek(2).value == Keyword(Kw::Is) && p.peek(3).value == Keyword(Kw::New) {
				Some(ast::DeclItem::PkgInst(parse_package_inst(p, true)?))
			} else {
				Some(ast::DeclItem::PkgDecl(parse_package_decl(p)?))
			}
		}
		// type_decl := "type" ...
		Keyword(Kw::Type) => Some(ast::DeclItem::TypeDecl(parse_type_decl(p, true)?)),
		// subtype_decl := "subtype" ...
		Keyword(Kw::Subtype) => Some(ast::DeclItem::SubtypeDecl(parse_subtype_decl(p)?)),
		// constant_decl := "constant" ...
		// signal_decl   := "signal" ...
		// variable_decl := ("variable"|"shared") ...
		// file_decl     := "file" ...
		Keyword(Kw::Constant) |
		Keyword(Kw::Signal) |
		Keyword(Kw::Variable) |
		Keyword(Kw::Shared) |
		Keyword(Kw::File) => Some(ast::DeclItem::ObjDecl(parse_object_decl(p)?)),
		// alias_decl := "alias" ...
		Keyword(Kw::Alias) => Some(ast::DeclItem::AliasDecl(parse_alias_decl(p)?)),
		// use_clause := "use" ...
		Keyword(Kw::Use) => Some(ast::DeclItem::UseClause(span, parse_use_clause(p)?)),
		// subprog_spec := "pure"|"impure"|"procedure"|"function" ...
		Keyword(Kw::Pure) |
		Keyword(Kw::Impure) |
		Keyword(Kw::Procedure) |
		Keyword(Kw::Function) => Some(ast::DeclItem::SubprogDecl(parse_subprog_decl_item(p)?)),
		// component_decl := "component" ...
		Keyword(Kw::Component) => Some(ast::DeclItem::CompDecl(parse_component_decl(p)?)),
		// discon_spec := "disconnect" ...
		Keyword(Kw::Disconnect) => Some(ast::DeclItem::DisconDecl(parse_discon_spec(p)?)),
		// config_spec := "for" ...
		Keyword(Kw::For) => Some(ast::DeclItem::CfgSpec(parse_config_spec(p)?)),
		// attr_decl := "attribute" ...
		Keyword(Kw::Attribute) => Some(ast::DeclItem::AttrDecl(parse_attr_decl(p)?)),
		// generic_clause     := "generic" ...
		// generic_map_aspect := "generic" "map" ...
		Keyword(Kw::Generic) => {
			let pk = Spanned::new(ast::PortgenKind::Generic, p.peek(0).span);
			if p.peek(1).value == Keyword(Kw::Map) {
				let a = try_map_aspect(p, Kw::Generic)?.unwrap();
				require(p, Semicolon)?;
				span.expand(p.last_span());
				Some(ast::DeclItem::PortgenMap(span, pk, a))
			} else {
				let c = try_generic_clause(p)?.unwrap();
				span.expand(p.last_span());
				Some(ast::DeclItem::PortgenClause(span, pk, c))
			}
		}
		// port_clause     := "port" ...
		// port_map_aspect := "port" "map" ...
		Keyword(Kw::Port) => {
			let pk = Spanned::new(ast::PortgenKind::Port, p.peek(0).span);
			if p.peek(1).value == Keyword(Kw::Map) {
				let a = try_map_aspect(p, Kw::Port)?.unwrap();
				require(p, Semicolon)?;
				span.expand(p.last_span());
				Some(ast::DeclItem::PortgenMap(span, pk, a))
			} else {
				let c = try_port_clause(p)?.unwrap();
				span.expand(p.last_span());
				Some(ast::DeclItem::PortgenClause(span, pk, c))
			}
		}
		// group_decl := "group" ...
		Keyword(Kw::Group) => Some(ast::DeclItem::GroupDecl(parse_group_decl(p)?)),
		_ => None
	})
}


/// Parse a subprogram declarative item, which is either a subprogram
/// declaration, body, or instantiation. See IEEE 1076-2008 section 4.2.
///
/// ```text
/// subprog_decl := subprog_spec ";"
/// subprog_body := subprog_spec "is" ...
/// subprog_inst := subprog_spec "is" "new" name [signature] [generic_map_aspect] ";"
/// ```
pub fn parse_subprog_decl_item<P: Parser>(p: &mut P) -> ReportedResult<ast::Subprog> {
	let mut span = p.peek(0).span;
	let spec = parse_subprog_spec(p)?;

	// Try to parse a subprogram declaration.
	if accept(p, Semicolon) {
		span.expand(p.last_span());
		return Ok(ast::Subprog{
			id: Default::default(),
			span: span,
			spec: spec,
			data: ast::SubprogData::Decl,
		});
	}

	// Try to parse a subprogram body or instantiation.
	if accept(p, Keyword(Kw::Is)) {
		// Try to parse a subprogram instantiation. Otherwise fall back to a
		// subprogram body.
		if accept(p, Keyword(Kw::New)) {
			let name = parse_name(p)?;
			let gm = try_map_aspect(p, Kw::Generic)?;
			require(p, Semicolon)?;
			span.expand(p.last_span());
			return Ok(ast::Subprog{
				id: Default::default(),
				span: span,
				spec: spec,
				data: ast::SubprogData::Inst{
					name: name,
					generics: gm,
				}
			});
		} else {
			let decl_items = repeat(p, try_decl_item)?;
			require(p, Keyword(Kw::Begin))?;
			let stmts = repeat_until(p, Keyword(Kw::End), parse_stmt)?;
			require(p, Keyword(Kw::End))?;
			// TODO: Check if things match once the subprog_spec returns
			// something useful.
			accept(p, Keyword(Kw::Function));
			accept(p, Keyword(Kw::Procedure));
			try_primary_name(p);
			require(p, Semicolon)?;
			span.expand(p.last_span());
			return Ok(ast::Subprog{
				id: Default::default(),
				span: span,
				spec: spec,
				data: ast::SubprogData::Body{
					decls: decl_items,
					stmts: stmts,
				}
			});
		}
	}

	// If we arrive here, none of the above matched. Emit an error that
	// describes what we expected.
	let pk = p.peek(0);
	p.emit(
		DiagBuilder2::error(format!("Expected `;` or keyword `is` after subprogram specification, found {} instead", pk.value))
		.span(pk.span)
		.add_note("see IEEE 1076-2008 section 4.2")
	);
	Err(Reported)
}


/// Parse a subtype indication. See IEEE 1076-2008 section 6.3.
///
/// ```text
/// subtype_ind
///   := name
///   := name name
///   := paren_expr name
/// ```
pub fn parse_subtype_ind<P: Parser>(p: &mut P) -> ReportedResult<ast::SubtypeInd> {
	let Spanned{ value: tkn, mut span } = p.peek(0);

	// Try to determine if the subtype indication starts out with a resolution
	// indication. This might either be another name in front of the subtype
	// name, or a element resolution in parenthesis.
	let (res, name) = if let Some(exprs) = try_paren_expr(p)? {
		let name = parse_name(p)?;
		(Some(ast::ResolInd::Exprs(exprs)), name)
	} else {
		let name = parse_name(p)?;
		if let Some(other) = try_name(p)? {
			(Some(ast::ResolInd::Name(name)), other)
		} else {
			(None, name)
		}
	};

	span.expand(p.last_span());
	Ok(ast::SubtypeInd{
		span: span,
		res: res,
		name: name,
	})
}


/// Try to parse a parenthesized expression. This is a combination of a variety
/// of rules from the VHDL grammar. Most notably, it combines the following:
///
/// - `aggregate`
/// - `association_list`
/// - suffix of `slice_name`
/// - suffix of `indexed_name`
/// - suffix of `function_call`
///
/// ```text
/// paren_expr := "(" { [ { expr }"|"+ "=>" ] expr }","+ ")"
/// ```
pub fn parse_paren_expr<P: Parser>(p: &mut P) -> ReportedResult<ast::ParenElems> {
	let mut span = p.peek(0).span;
	let v = flanked(p, Paren, parse_paren_elem_vec)?;
	span.expand(p.last_span());
	Ok(Spanned::new(v, span))
}


pub fn try_paren_expr<P: Parser>(p: &mut P) -> ReportedResult<Option<ast::ParenElems>> {
	let mut span = p.peek(0).span;
	match try_flanked(p, Paren, parse_paren_elem_vec)? {
		Some(v) => {
			span.expand(p.last_span());
			Ok(Some(Spanned::new(v, span)))
		}
		None => {
			Ok(None)
		}
	}
}


pub fn parse_paren_elem_vec<P: Parser>(p: &mut P) -> ReportedResult<Vec<ast::ParenElem>> {
	separated(p, Comma, CloseDelim(Paren), "expression", |p|{
		// Parse a list of choices, i.e. expressions separated by `|`.
		let mut choices = separated_nonempty(p, Pipe, token_predicate!(Arrow, Comma, CloseDelim(Paren)), "expression", parse_expr)?;

		// If the expressions are followed by a "=>", what we have parsed is a
		// list of choices. Otherwise, ensure that there is only one expression
		// in the list.
		if accept(p, Arrow) {
			let q = p.last_span();
			let actual = parse_expr(p)?;
			let span = Span::union(choices[0].span, actual.span);
			Ok(ast::ParenElem{
				span: span,
				choices: choices,
				expr: actual,
			})
		} else {
			let mut it = choices.drain(..);
			let first = it.next().unwrap();

			// Emit errors for additional expressions.
			let mut it = it.map(|x| x.span);
			if let Some(second) = it.next() {
				let span = it.fold(second, Span::union);
				p.emit(
					DiagBuilder2::error("Superfluous additional expressions")
					.span(span)
					.add_note("If you wanted an association list, did you forget a `=>` after the list of choices?")
				);
				return Err(Reported);
			}

			let span = first.span;
			Ok(ast::ParenElem{
				span: span,
				choices: vec![],
				expr: first,
			})
		}
	}).map_err(|e| e.into())
}


pub fn parse_expr<P: Parser>(p: &mut P) -> ReportedResult<ast::Expr> {
	parse_expr_prec(p, ExprPrec::lowest())
}


pub fn parse_primary_expr<P: Parser>(p: &mut P) -> ReportedResult<ast::Expr> {
	let Spanned{ value: tkn, mut span } = p.peek(0);

	// Try to handle the easy cases where the next token clearly identifies the
	// kind of primary expression that follows.
	if let Some(data) = match tkn {
		Keyword(Kw::Null) => { p.bump(); Some(ast::NullExpr) },
		Keyword(Kw::Open) => { p.bump(); Some(ast::OpenExpr) },
		Keyword(Kw::Others) => { p.bump(); Some(ast::OthersExpr) },
		Keyword(Kw::Default) => { p.bump(); Some(ast::DefaultExpr) },
		LtGt => { p.bump(); Some(ast::BoxExpr) },

		Keyword(Kw::New) => {
			p.bump();
			let expr = parse_primary_expr(p)?;
			Some(ast::NewExpr(Box::new(expr)))
			// let mut expr_span = p.peek(0).span;

			// // Try to parse a name or qualified expression.
			// if let Some(expr) = try_name_or_qualified_primary_expr(p)? {
			// 	span.expand(p.last_span());
			// 	Some(ast::NewExpr(expr))
			// }

			// // Try to parse a name prefixed by parenthesis.
			// else if let Some(paren) = try_paren_expr(p)? {
			// 	let name = parse_name(p)?;
			// 	span.expand(p.last_span());
			// 	expr_span.expand(p.last_span());
			// 	Some(ast::NewExpr(ast::Expr{
			// 		span: expr_span,
			// 		data: ast::ParenPrefixExpr(paren, )
			// 	}))
			// }

			// // Throw an error.
			// else {
			// 	p.emit(
			// 		DiagBuilder2::error("Expected subtype or qualified expression after `new`")
			// 		.span(span)
			// 	);
			// 	return Err(Reported);
			// }
		}

		Lit(l @ Literal::Abstract(_, _, _, _)) => {
			p.bump();
			let unit = try_name(p)?;
			span.expand(p.last_span());
			Some(ast::LitExpr(l, unit))
		}

		Lit(l @ Literal::BitString(_, _, _)) => {
			p.bump();
			Some(ast::LitExpr(l, None))
		}

		OpenDelim(Paren) => {
			let expr = parse_paren_expr(p)?;

			// Try to parse a name, which caters for the case of subtype
			// indications that are prefixed with element resolution.
			if let Some(name) = try_name(p)? {
				span.expand(p.last_span());
				Some(ast::ResolExpr(expr, name))
			} else {
				span.expand(p.last_span());
				Some(ast::ParenExpr(expr))
			}
		}

		_ => None
	}{
		return Ok(ast::Expr{
			span: span,
			data: data,
		});
	}

	// Try to parse a name-prefixed primary expression.
	if let Some(expr) = try_name_or_qualified_primary_expr(p)? {
		return Ok(expr);
	}

	// If we arrive here, nothing matched. Emit an error that describes what a
	// primary expression may entail.
	let q = p.peek(0).span;
	p.emit(
		DiagBuilder2::error(format!("Expected a primary expression, found {} instead", tkn))
		.span(q)
		.add_note("A primary expression is either an abstract, bit string, character, or string literal; a name; a parenthesized expression `( ... )`; an allocation `new ...`; or the constants `null`, `open`, or `others`.")
	);
	Err(Reported)
}


pub fn try_name_or_qualified_primary_expr<P: Parser>(p: &mut P) -> ReportedResult<Option<ast::Expr>> {
	let span = p.peek(0).span;

	// Try to parse a name.
	if let Some(name) = try_name(p)? {
		// Try to parse another name, for things that look like element
		// resolutions.
		if let Some(suffix_name) = try_name(p)? {
			return Ok(Some(ast::Expr{
				span: span,
				data: ast::DoubleNameExpr(name, suffix_name),
			}));
		}

		// Try to parse a `'`, which would make this a qualified expression.
		if accept(p, Apostrophe) {
			if p.peek(0).value == OpenDelim(Paren) {
				let expr = parse_paren_expr(p)?;
				return Ok(Some(ast::Expr{
					span: span,
					data: ast::QualExpr(name, expr),
				}));
			} else {
				let q = p.last_span();
				p.emit(
					DiagBuilder2::error("Expected a parenthesized expression after `'`")
					.span(q)
					.add_note("`'` introduces a qualified expression, which is of the form `<name>'(<expr>)`")
					.add_note("see IEEE 1076-2008 section 9.3.5")
				);
				return Err(Reported);
			}
		}

		return Ok(Some(ast::Expr{
			span: span,
			data: ast::NameExpr(name),
		}));
	}

	Ok(None)
}


/// The precedence of an expression.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExprPrec {
	Inertial,
	Condition,
	Logical,
	Relational,
	Shift,
	Range,
	Add,
	Sign,
	Mul,
	Pow,
	Unary,
	Primary,
}

impl ExprPrec {
	fn highest() -> ExprPrec {
		ExprPrec::Primary
	}

	fn lowest() -> ExprPrec {
		ExprPrec::Inertial
	}
}


/// Parse an expression with a precedence higher than `prec`.
///
/// ```text
/// expr[10] := "inertial" expr[9]
/// ```
pub fn parse_expr_prec<P: Parser>(p: &mut P, prec: ExprPrec) -> ReportedResult<ast::Expr> {
	let Spanned{ value: tkn, mut span } = p.peek(0);

	// Try to parse a unary operator.
	if let Some(op) = as_unary_op(tkn) {
		let op_prec = unary_prec(op);
		if prec <= op_prec {
			p.bump();
			let arg = parse_expr_prec(p, op_prec)?;
			span.expand(p.last_span());
			return parse_expr_suffix(p, ast::Expr{
				span: span,
				data: ast::UnaryExpr(op, Box::new(arg)),
			}, prec);
		}
	}

	// Parse a primary expression.
	let primary = parse_primary_expr(p)?;

	// Parse any optional expression suffix.
	parse_expr_suffix(p, primary, prec)
}


/// Parse an expression suffix. Given an already parsed expression and its
/// precedence, try to parse additional tokens that extend the already parsed
/// expression. This is currently limited to binary operations.
pub fn parse_expr_suffix<P: Parser>(p: &mut P, prefix: ast::Expr, prec: ExprPrec) -> ReportedResult<ast::Expr> {
	let tkn = p.peek(0).value;

	// Try to parse a binary operation.
	if let Some(op) = as_binary_op(tkn) {
		let op_prec = binary_prec(op);
		if prec <= op_prec {
			p.bump();
			let rhs = parse_expr_prec(p, op_prec)?;
			let span = Span::union(prefix.span, p.last_span());
			return parse_expr_suffix(p, ast::Expr{
				span: span,
				data: ast::BinaryExpr(op, Box::new(prefix), Box::new(rhs)),
			}, prec);
		}
	}

	// If we arrive here, none of the suffices matched, so we simply return the
	// expression that we have received.
	Ok(prefix)
}


/// Try to interpret a token as a unary operator.
fn as_unary_op(tkn: Token) -> Option<ast::UnaryOp> {
	Some(match tkn {
		Keyword(Kw::Inertial) => ast::UnaryOp::Inertial,
		Condition             => ast::UnaryOp::Condition,

		Keyword(Kw::Not)      => ast::UnaryOp::Not,
		Keyword(Kw::Abs)      => ast::UnaryOp::Abs,

		Add                   => ast::UnaryOp::Sign(ast::Sign::Pos),
		Sub                   => ast::UnaryOp::Sign(ast::Sign::Neg),

		Keyword(Kw::And)      => ast::UnaryOp::Logical(ast::LogicalOp::And),
		Keyword(Kw::Or)       => ast::UnaryOp::Logical(ast::LogicalOp::Or),
		Keyword(Kw::Nand)     => ast::UnaryOp::Logical(ast::LogicalOp::Nand),
		Keyword(Kw::Nor)      => ast::UnaryOp::Logical(ast::LogicalOp::Nor),
		Keyword(Kw::Xor)      => ast::UnaryOp::Logical(ast::LogicalOp::Xor),
		Keyword(Kw::Xnor)     => ast::UnaryOp::Logical(ast::LogicalOp::Xnor),
		_ => return None
	})
}

/// Try to interpret a token as a binary operator.
fn as_binary_op(tkn: Token) -> Option<ast::BinaryOp> {
	Some(match tkn {
		Keyword(Kw::To)       => ast::BinaryOp::Dir(ast::Dir::To),
		Keyword(Kw::Downto)   => ast::BinaryOp::Dir(ast::Dir::Downto),

		Keyword(Kw::And)      => ast::BinaryOp::Logical(ast::LogicalOp::And),
		Keyword(Kw::Or)       => ast::BinaryOp::Logical(ast::LogicalOp::Or),
		Keyword(Kw::Nand)     => ast::BinaryOp::Logical(ast::LogicalOp::Nand),
		Keyword(Kw::Nor)      => ast::BinaryOp::Logical(ast::LogicalOp::Nor),
		Keyword(Kw::Xor)      => ast::BinaryOp::Logical(ast::LogicalOp::Xor),
		Keyword(Kw::Xnor)     => ast::BinaryOp::Logical(ast::LogicalOp::Xnor),

		Eq                    => ast::BinaryOp::Rel(ast::RelationalOp::Eq),
		Neq                   => ast::BinaryOp::Rel(ast::RelationalOp::Neq),
		Lt                    => ast::BinaryOp::Rel(ast::RelationalOp::Lt),
		Leq                   => ast::BinaryOp::Rel(ast::RelationalOp::Leq),
		Gt                    => ast::BinaryOp::Rel(ast::RelationalOp::Gt),
		Geq                   => ast::BinaryOp::Rel(ast::RelationalOp::Geq),

		MatchEq               => ast::BinaryOp::Match(ast::RelationalOp::Eq),
		MatchNeq              => ast::BinaryOp::Match(ast::RelationalOp::Neq),
		MatchLt               => ast::BinaryOp::Match(ast::RelationalOp::Lt),
		MatchLeq              => ast::BinaryOp::Match(ast::RelationalOp::Leq),
		MatchGt               => ast::BinaryOp::Match(ast::RelationalOp::Gt),
		MatchGeq              => ast::BinaryOp::Match(ast::RelationalOp::Geq),

		Keyword(Kw::Sll)      => ast::BinaryOp::Shift(ast::ShiftOp::Sll),
		Keyword(Kw::Srl)      => ast::BinaryOp::Shift(ast::ShiftOp::Srl),
		Keyword(Kw::Sla)      => ast::BinaryOp::Shift(ast::ShiftOp::Sla),
		Keyword(Kw::Sra)      => ast::BinaryOp::Shift(ast::ShiftOp::Sra),
		Keyword(Kw::Rol)      => ast::BinaryOp::Shift(ast::ShiftOp::Rol),
		Keyword(Kw::Ror)      => ast::BinaryOp::Shift(ast::ShiftOp::Ror),

		Add                   => ast::BinaryOp::Add,
		Sub                   => ast::BinaryOp::Sub,
		Ampersand             => ast::BinaryOp::Concat,

		Mul                   => ast::BinaryOp::Mul,
		Div                   => ast::BinaryOp::Div,
		Keyword(Kw::Mod)      => ast::BinaryOp::Mod,
		Keyword(Kw::Rem)      => ast::BinaryOp::Rem,
		Pow                   => ast::BinaryOp::Pow,
		_ => return None
	})
}

/// Obtain the precedence of a unary operator.
fn unary_prec(op: ast::UnaryOp) -> ExprPrec {
	match op {
		ast::UnaryOp::Not        => ExprPrec::Unary,
		ast::UnaryOp::Abs        => ExprPrec::Unary,
		ast::UnaryOp::Logical(_) => ExprPrec::Unary,
		ast::UnaryOp::Sign(_)    => ExprPrec::Sign,
		ast::UnaryOp::Inertial   => ExprPrec::Inertial,
		ast::UnaryOp::Condition  => ExprPrec::Condition,
	}
}

/// Obtain the precedence of a binary operator.
fn binary_prec(op: ast::BinaryOp) -> ExprPrec {
	match op {
		ast::BinaryOp::Dir(_)     => ExprPrec::Range,
		ast::BinaryOp::Logical(_) => ExprPrec::Logical,
		ast::BinaryOp::Rel(_)     => ExprPrec::Relational,
		ast::BinaryOp::Match(_)   => ExprPrec::Relational,
		ast::BinaryOp::Shift(_)   => ExprPrec::Shift,
		ast::BinaryOp::Add        => ExprPrec::Add,
		ast::BinaryOp::Sub        => ExprPrec::Add,
		ast::BinaryOp::Concat     => ExprPrec::Add,
		ast::BinaryOp::Mul        => ExprPrec::Mul,
		ast::BinaryOp::Div        => ExprPrec::Mul,
		ast::BinaryOp::Mod        => ExprPrec::Mul,
		ast::BinaryOp::Rem        => ExprPrec::Mul,
		ast::BinaryOp::Pow        => ExprPrec::Pow,
	}
}


/// Parse a package declaration. See IEEE 1076-2008 section 4.7.
///
/// ```text
/// package_decl :=
///   "package" ident "is"
///     [generic_clause [generic_map_aspect ";"]]
///     {decl_item}
///   "end" ["package"] [ident] ";"
/// ```
pub fn parse_package_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::PkgDecl> {
	let mut span = p.peek(0).span;

	// Parse the head of the declaration.
	require(p, Keyword(Kw::Package))?;
	let name = parse_ident(p, "package name")?;
	require(p, Keyword(Kw::Is))?;

	// Parse the declarative part.
	let decl_items = repeat(p, try_decl_item)?;

	// Parse the tail of the declaration.
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Package));
	parse_optional_matching_ident(p, name, "package", "section 4.7");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::PkgDecl{
		id: Default::default(),
		span: span,
		name: name,
		decls: decl_items,
	})
}


/// Parse a package body. See IEEE 1076-2008 section 4.8.
///
/// ```text
/// package_decl :=
///   "package" "body" ident "is"
///     {decl_item}
///   "end" ["package" "body"] [ident] ";"
/// ```
pub fn parse_package_body<P: Parser>(p: &mut P) -> ReportedResult<ast::PkgBody> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Package))?;
	require(p, Keyword(Kw::Body))?;
	let name = parse_ident(p, "package name")?;
	require(p, Keyword(Kw::Is))?;
	let decl_items = repeat(p, try_decl_item)?;
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Package)); // TODO: add proper warnings if these are missing
	accept(p, Keyword(Kw::Body)); // TODO: add proper warnings if these are missing
	parse_optional_matching_ident(p, name, "package body", "section 4.8");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::PkgBody{
		id: Default::default(),
		span: span,
		name: name,
		decls: decl_items,
	})
}


/// Parse a package instantiation declaration. See IEEE 1076-2008 section 4.9.
///
/// ```text
/// package_inst := "package" ident "is" "new" name [generic_map] ";"
/// ```
pub fn parse_package_inst<P: Parser>(p: &mut P, with_semicolon: bool) -> ReportedResult<ast::PkgInst> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Package))?;
	let name = parse_ident(p, "package name")?;
	require(p, Keyword(Kw::Is))?;
	require(p, Keyword(Kw::New))?;
	let pkg = parse_name(p)?;
	let gm = try_map_aspect(p, Kw::Generic)?;
	if with_semicolon {
		require(p, Semicolon)?;
	}
	span.expand(p.last_span());
	Ok(ast::PkgInst{
		id: Default::default(),
		span: span,
		name: name,
		target: pkg,
		generics: gm,
	})
}


/// Try to parse a generic or port map aspect. See IEEE 1076-2008 sections
/// 6.5.7.2 and 6.5.7.3.
///
/// ```text
/// map_aspect := ["generic"|"port"] "map" paren_expr
/// ```
pub fn try_map_aspect<P: Parser>(p: &mut P, kw: Kw) -> ReportedResult<Option<ast::ParenElems>> {
	if p.peek(0).value == Keyword(kw) && p.peek(1).value == Keyword(Kw::Map) {
		p.bump();
		p.bump();
		let v = parse_paren_expr(p)?;
		Ok(Some(v))
	} else {
		Ok(None)
	}
}


/// Parse a type declaration. See IEEE 1076-2008 section 6.2.
///
/// ```text
/// type_decl := "type" ident ["is" type_def] ";"
/// type_def
///   := paren_expr
///   := "range" range
///   := "range" range units_decl
///   := "array" paren_expr "of" subtype_ind
///   := "record" {{ident}","+ ":" subtype_ind ";"}+ "end" "record" [ident]
///   := "access" subtype_ind
///   := "file" "of" name
///   := protected_type_decl
///   := protected_type_body
/// ```
pub fn parse_type_decl<P: Parser>(p: &mut P, with_semicolon: bool) -> ReportedResult<ast::TypeDecl> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Type))?;
	let name = parse_ident(p, "type name")?;

	// Parse the optional type definition. If present, this is a full type
	// declaration. Otherwise it is an incomplete type declaration.
	let data = if accept(p, Keyword(Kw::Is)) {
		let Spanned{ value: tkn, span: sp } = p.peek(0);
		Some(match tkn {
			// Enumeration type definition
			OpenDelim(Paren) => ast::EnumType(parse_paren_expr(p)?),

			// Integer, float, physical type definition
			Keyword(Kw::Range) => {
				p.bump();
				let range = parse_expr(p)?;
				let units = if accept(p, Keyword(Kw::Units)) {
					let u = repeat_until(p, Keyword(Kw::End), |p|{
						let name = parse_ident(p, "unit name")?;
						let rel = if accept(p, Eq) {
							Some(Box::new(parse_expr(p)?))
						} else {
							None
						};
						require(p, Semicolon)?;
						Ok((name.into(), rel))
					})?;
					require(p, Keyword(Kw::End))?;
					require(p, Keyword(Kw::Units))?;
					parse_optional_matching_ident(p, name, "type", "section 5.2.4");
					Some(u)
				} else {
					None
				};
				ast::RangeType(Box::new(range), units)
			}

			// Array type definition
			Keyword(Kw::Array) => {
				p.bump();
				let indices = parse_paren_expr(p)?;
				require(p, Keyword(Kw::Of))?;
				let subtype = parse_subtype_ind(p)?;
				ast::ArrayType(indices, subtype)
			}

			// Record type definition
			Keyword(Kw::Record) => {
				p.bump();
				let fields = repeat_until(p, Keyword(Kw::End), |p|{
					let names = separated_nonempty(p,
						Comma,
						Colon,
						"field name",
						|p| parse_ident(p, "field name").map(|i| i.into())
					)?;
					require(p, Colon)?;
					let subtype = parse_subtype_ind(p)?;
					require(p, Semicolon)?;
					Ok((names, subtype))
				})?;
				require(p, Keyword(Kw::End))?;
				require(p, Keyword(Kw::Record))?;
				parse_optional_matching_ident(p, name, "type", "section 5.3.3");
				ast::RecordType(fields)
			}

			// Access type definition
			Keyword(Kw::Access) => {
				p.bump();
				let subtype = parse_subtype_ind(p)?;
				ast::AccessType(subtype)
			}

			// File type definition
			Keyword(Kw::File) => {
				p.bump();
				require(p, Keyword(Kw::Of))?;
				let ty = parse_name(p)?;
				ast::FileType(ty)
			}

			// Protected type declaration and body
			Keyword(Kw::Protected) => {
				p.bump();
				let body = accept(p, Keyword(Kw::Body));
				let decl_items = repeat(p, try_decl_item)?;
				require(p, Keyword(Kw::End))?;
				require(p, Keyword(Kw::Protected))?;
				if body {
					require(p, Keyword(Kw::Body))?;
				}
				parse_optional_matching_ident(p, name, "type", "section 5.6");
				ast::ProtectedType(decl_items)
			}

			// Emit an error for anything else.
			wrong => {
				p.emit(
					DiagBuilder2::error(format!("Expected type definition after keyword `is`, found {} instead", tkn))
					.span(sp)
				);
				return Err(Reported);
			}
		})
	} else {
		None
	};

	if with_semicolon {
		require(p, Semicolon)?;
	}
	span.expand(p.last_span());
	Ok(ast::TypeDecl{
		id: Default::default(),
		span: span,
		name: name,
		data: data,
	})
}


/// Parse a subtype declaration. See IEEE 1076-2008 section 6.3.
///
/// ```text
/// subtype_decl := "subtype" ident "is" subtype_ind ";"
/// ```
pub fn parse_subtype_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::SubtypeDecl> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Subtype))?;
	let name = parse_ident(p, "subtype name")?;
	require(p, Keyword(Kw::Is))?;
	let subtype = parse_subtype_ind(p)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::SubtypeDecl{
		id: Default::default(),
		span: span,
		name: name,
		subtype: subtype,
	})
}


/// Parse an alias declaration. See IEEE 1076-2008 section 6.6.
///
/// ```text
/// alias_decl := "alias" alias_desig [":" subtype_ind] "is" name [signature] ";"
/// alias_desig := ident | char_lit | string_lit
/// ```
pub fn parse_alias_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::AliasDecl> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Alias))?;
	let name = match try_primary_name(p) {
		Some(n) => n,
		None => {
			let pk = p.peek(0);
			p.emit(
				DiagBuilder2::error(format!("Expected alias designator after keyword `alias`, found {} instead", pk.value))
				.span(pk.span)
				.add_note("An alias designator is either an identifier, a character literal, or an operator symbol")
				.add_note("see IEEE 1076-2008 section 6.6")
			);
			return Err(Reported);
		}
	};
	let subtype = if accept(p, Colon) {
		Some(parse_subtype_ind(p)?)
	} else {
		None
	};
	require(p, Keyword(Kw::Is))?;
	let target = parse_name(p)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::AliasDecl{
		id: Default::default(),
		span: span,
		name: name,
		subtype: subtype,
		target: target,
	})
}


pub fn parse_signature<P: Parser>(p: &mut P) -> ReportedResult<ast::Signature> {
	let mut span = p.last_span();
	let args = separated(
		p,
		Comma,
		token_predicate!(CloseDelim(Brack), Keyword(Kw::Return)),
		"type mark",
		parse_name,
	)?;
	let retty = if accept(p, Keyword(Kw::Return)) {
		Some(parse_name(p)?)
	} else {
		None
	};
	span.expand(p.peek(0).span);
	Ok(ast::Signature{
		span: span,
		args: args,
		retty: retty,
	})
}


/// Parse a constant, signal, variable, or file declaration. See IEEE 1076-2008
/// section 6.4.2.
///
/// ```text
/// object_decl := object_kind {ident}","+ ":" subtype_ind [object_details] [":=" expr] ";"
/// object_kind
///   := "constant"
///   := "signal"
///   := "variable"
///   := "shared" "variable"
///   := "file"
/// object_details
///   := "register"
///   := "bus"
///   := ["open" expr] "is" expr
/// ```
pub fn parse_object_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::ObjDecl> {
	let mut span = p.peek(0).span;

	// Parse the object kind.
	let kind = match p.peek(0).value {
		Keyword(Kw::Constant) => { p.bump(); ast::ObjKind::Const },
		Keyword(Kw::Signal)   => { p.bump(); ast::ObjKind::Signal },
		Keyword(Kw::File)     => { p.bump(); ast::ObjKind::File },
		Keyword(Kw::Variable) => { p.bump(); ast::ObjKind::Var },
		Keyword(Kw::Shared)   => {
			p.bump();
			require(p, Keyword(Kw::Variable))?;
			ast::ObjKind::SharedVar
		}
		wrong => {
			p.emit(
				DiagBuilder2::error(format!("Expected a constant, signal, variable, or file declaration, found {} instead", wrong))
				.span(span)
				.add_note("see IEEE 1076-2008 section 6.4.2")
			);
			return Err(Reported);
		}
	};

	// Parse the name list and subtype indication.
	let names = separated_nonempty(p, Comma, Colon, "object name", |p| parse_ident(p, "object name"))?;
	require(p, Colon)?;
	let subtype = parse_subtype_ind(p)?;

	// Parse the additional object details.
	let pk = p.peek(0);
	let detail = match pk.value {
		Keyword(Kw::Register) => { p.bump(); Some(Spanned::new(ast::ObjDetail::Register, p.last_span())) },
		Keyword(Kw::Bus) => { p.bump(); Some(Spanned::new(ast::ObjDetail::Bus, p.last_span())) },
		Keyword(Kw::Open) | Keyword(Kw::Is) => {
			let mut span = p.peek(0).span;
			let open = if accept(p, Keyword(Kw::Open)) {
				Some(parse_expr(p)?)
			} else {
				None
			};
			require(p, Keyword(Kw::Is))?;
			let path = parse_expr(p)?;
			span.expand(p.last_span());
			Some(Spanned::new(ast::ObjDetail::Open(open, path), span))
		}
		_ => None
	};

	// Parse the optional initial expression.
	let init = if accept(p, VarAssign) {
		Some(parse_expr(p)?)
	} else {
		None
	};

	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::ObjDecl{
		span: span,
		kind: kind,
		names: names.into_iter().map(|n| n.into()).collect(),
		subtype: subtype,
		detail: detail,
		init: init,
	})
}


/// Parse a subprogram specification. This covers the initial part of a
/// subprogram declaration, body, instantiation, or interface declaration. See
/// IEEE 1076-2008 sections 4.2 and 6.5.4. Note that not all combinations of
/// keywords and qualifiers that this parser accepts are actually valid.
///
/// ```text
/// subprog_spec :=
///   ["pure"|"impure"] "procedure"|"function" primary_name
///   ["generic" paren_expr]
///   ["generic" "map" paren_expr]
///   [["parameter"] paren_expr]
///   ["return" name]
/// ```
pub fn parse_subprog_spec<P: Parser>(p: &mut P) -> ReportedResult<ast::SubprogSpec> {
	let mut span = p.peek(0).span;

	// Parse the optional purity qualifier.
	let purity = match p.peek(0).value {
		Keyword(Kw::Pure) => { p.bump(); Some(ast::SubprogPurity::Pure) },
		Keyword(Kw::Impure) => { p.bump(); Some(ast::SubprogPurity::Impure) },
		_ => None
	};

	// Parse the subprogram kind.
	let pk = p.peek(0);
	let kind = match pk.value {
		Keyword(Kw::Procedure) => { p.bump(); ast::SubprogKind::Proc },
		Keyword(Kw::Function) => { p.bump(); ast::SubprogKind::Func },
		wrong => {
			p.emit(
				DiagBuilder2::error(format!("Expected `procedure` or `function`, found {} instead", wrong))
				.span(span)
				.add_note("see IEEE 1076-2008 section 4.2")
			);
			return Err(Reported);
		}
	};

	// Parse the name.
	let name = match try_primary_name(p) {
		Some(n) => n,
		None => {
			let pk = p.peek(0);
			p.emit(
				DiagBuilder2::error(format!("Expected subprogram name, found {} instead", pk.value))
				.span(pk.span)
				.add_note("A subprogram name is either an identifier or an operator symbol")
				.add_note("see IEEE 1076-2008 section 4.2")
			);
			return Err(Reported);
		}
	};

	// Parse the optional generic clause.
	let gc = if p.peek(0).value == Keyword(Kw::Generic) && p.peek(1).value != Keyword(Kw::Map) {
		p.bump();
		Some(flanked(p, Paren, |p|{
			Ok(separated_nonempty(p,
				Semicolon,
				CloseDelim(Paren),
				"generic interface declaration",
				|p| parse_intf_decl(p, Some(ast::IntfObjKind::Const))
			)?)
		})?)
	} else {
		None
	};

	// Parse the optional generic map aspect.
	let gm = try_map_aspect(p, Kw::Generic)?;

	// Parse the optional parameter keyword and list.
	let params = if accept(p, Keyword(Kw::Parameter)) || p.peek(0).value == OpenDelim(Paren) {
		Some(flanked(p, Paren, |p|{
			Ok(separated_nonempty(p,
				Semicolon,
				CloseDelim(Paren),
				"parameter interface declaration",
				|p| parse_intf_decl(p, Some(ast::IntfObjKind::Var))
			)?)
		})?)
	} else {
		None
	};

	// Parse the optional return type.
	let retty = if accept(p, Keyword(Kw::Return)) {
		Some(parse_name(p)?)
	} else {
		None
	};

	span.expand(p.last_span());
	Ok(ast::SubprogSpec{
		span: span,
		name: name,
		kind: kind,
		purity: purity,
		generic_clause: gc,
		generic_map: gm,
		params: params,
		retty: retty,
	})
}


/// Parse a component declaration. See IEEE 1076-2008 section 6.8.
///
/// ```text
/// component_decl :=
///   "component" ident ["is"]
///     [generic_clause]
///     [port_clause]
///   "end" ["component"] [ident] ";"
/// ```
pub fn parse_component_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::CompDecl> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Component))?;
	let name = parse_ident(p, "component name")?;
	accept(p, Keyword(Kw::Is));
	let gc = try_generic_clause(p)?;
	let pc = try_port_clause(p)?;
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Component));
	parse_optional_matching_ident(p, name, "component", "section 6.8");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::CompDecl{
		id: Default::default(),
		span: span,
		name: name,
		generics: gc,
		ports: pc,
	})
}


/// Parse a disconnection specification. See IEEE 1076-2008 section 7.4.
///
/// ```text
/// discon_spec := "disconnect" signal_list ":" name "after" expr ";"
/// signal_list := {name}","+ | "others" | "all"
/// ```
pub fn parse_discon_spec<P: Parser>(p: &mut P) -> ReportedResult<ast::DisconSpec> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Disconnect))?;
	let target = match p.peek(0).value {
		Keyword(Kw::Others) => { p.bump(); ast::DisconTarget::Others },
		Keyword(Kw::All) => { p.bump(); ast::DisconTarget::All },
		_ => ast::DisconTarget::Signals(separated_nonempty(p, Comma, Colon, "signal name", parse_name)?),
	};
	require(p, Colon)?;
	let ty = parse_name(p)?;
	require(p, Keyword(Kw::After))?;
	let after = parse_expr(p)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::DisconSpec{
		span: span,
		target: target,
		ty: ty,
		after: after,
	})
}


pub fn parse_vunit_binding_ind<P: Parser>(p: &mut P) -> ReportedResult<()> {
	unimp!(p, "Verification unit binding indications")
}


/// Parse a block or component configuration declarative item.
///
/// ```text
/// block_decl_item
///   := use_clause
///   := attr_spec
///   := group_decl
///   := vunit_binding_ind
///   := block_comp_config
/// ```
pub fn parse_block_comp_decl_item<P: Parser>(p: &mut P) -> ReportedResult<ast::DeclItem> {
	match (p.peek(0).value, p.peek(1).value) {
		// vunit_binding_ind := "use" "vunit" ...
		(Keyword(Kw::Use), Keyword(Kw::Vunit)) => parse_vunit_binding_ind(p).map(|i| ast::DeclItem::VunitBindInd(i)),
		// use_clause := "use" ...
		(Keyword(Kw::Use), _) => {
			let span = p.peek(1).span;
			parse_use_clause(p).map(|i| ast::DeclItem::UseClause(span, i))
		}
		// block_comp_config := "for" ...
		(Keyword(Kw::For), _) => parse_block_comp_config(p).map(|i| ast::DeclItem::BlockCompCfg(i)),
		// attr_spec := "attribute" ...
		(Keyword(Kw::Attribute), _) => parse_attr_decl(p).map(|i| ast::DeclItem::AttrDecl(i)),
		// group_decl := "group" ...
		(Keyword(Kw::Group), _) => parse_group_decl(p).map(|i| ast::DeclItem::GroupDecl(i)),

		(wrong, _) => {
			let sp = p.peek(0).span;
			p.emit(
				DiagBuilder2::error(format!("Expected configuration item, found {} instead", wrong))
				.span(sp)
			);
			Err(Reported)
		}
	}
}


/// Parse a block or component configuration. See IEEE 1076-2008 sections 3.4.2
/// and 3.4.3.
///
/// ```text
/// block_comp_config := "for" block_comp_spec [binding_ind] {block_config_item} "end" "for" ";"
/// block_comp_spec := name | {ident}","+ ":" name | "others" ":" name | "all" ":" name
/// ```
pub fn parse_block_comp_config<P: Parser>(p: &mut P) -> ReportedResult<ast::BlockCompCfg> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::For))?;
	let spec = parse_block_comp_spec(p)?;
	let bind = parse_binding_ind(p)?;
	let decl_items = repeat_until(p, Keyword(Kw::End), parse_block_comp_decl_item)?;
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::For))?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::BlockCompCfg{
		span: span,
		spec: spec,
		bind: bind,
		decls: decl_items,
	})
}


/// Parse a binding indication. See IEEE 1076-2008 section 7.3.2.1. The trailing
/// semicolon is required only if at least one of the aspect has been parsed.
///
/// ```text
/// binding_ind := ["use" entity_aspect] [generic_map_aspect] [port_map_aspect] [";"]
/// entity_aspect
///   := "entity" name
///   := "configuration" name
///   := "open"
/// ```
pub fn parse_binding_ind<P: Parser>(p: &mut P) -> ReportedResult<ast::BindingInd> {
	let mut span = p.peek(0).span;

	// Parse the entity aspect.
	let entity = if accept(p, Keyword(Kw::Use)) {
		let pk = p.peek(0);
		Some(match pk.value {
			Keyword(Kw::Entity) => {
				p.bump();
				ast::EntityAspect::Entity(parse_name(p)?)
			}
			Keyword(Kw::Configuration) => {
				p.bump();
				ast::EntityAspect::Cfg(parse_name(p)?)
			}
			Keyword(Kw::Open) => {
				p.bump();
				ast::EntityAspect::Open
			}
			_ => {
				p.emit(
					DiagBuilder2::error(format!("Expected entity aspect after `use`, found {} instead", pk.value))
					.span(pk.span)
					.add_note("An entity aspect is one of the following:")
					.add_note("`entity <name>(<architecture>)`")
					.add_note("`configuration <name>`")
					.add_note("`open`")
					.add_note("see IEEE 1076-2008 section 7.3.2.2")
				);
				return Err(Reported);
			}
		})
	} else {
		None
	};

	// Parse the generic map aspect.
	let gm = try_map_aspect(p, Kw::Generic)?;

	// Parse the port map aspect.
	let pm = try_map_aspect(p, Kw::Port)?;

	if entity.is_some() || gm.is_some() || pm.is_some() {
		require(p, Semicolon)?;
	}
	span.expand(p.last_span());
	Ok(ast::BindingInd{
		span: span,
		entity: entity,
		generics: gm,
		ports: pm,
	})
}


/// Parse a block or component specification. See IEEE 1067-2008 section 7.3.1.
///
/// ```text
/// block_comp_spec
///   := name
///   := {ident}","+ ":" name
///   := "others" ":" name
///   := "all" ":" name
/// ```
pub fn parse_block_comp_spec<P: Parser>(p: &mut P) -> ReportedResult<Spanned<ast::BlockCompSpec>> {
	let mut span = p.peek(0).span;

	// Try to detect if this is a block or component specification.
	let spec = match (p.peek(0).value, p.peek(1).value) {
		(Keyword(Kw::Others), _) => {
			p.bump();
			require(p, Colon)?;
			let name = parse_name(p)?;
			ast::BlockCompSpec::CompOthers(name)
		},

		(Keyword(Kw::All), _) => {
			p.bump();
			require(p, Colon)?;
			let name = parse_name(p)?;
			ast::BlockCompSpec::CompAll(name)
		}

		(Ident(_), Comma) | (Ident(_), Colon) => {
			let names = separated_nonempty(
				p,
				Comma,
				Colon,
				"label",
				|p| parse_ident(p, "label").map(|n| n.into())
			)?;
			require(p, Colon)?;
			let name = parse_name(p)?;
			ast::BlockCompSpec::CompNames(names, name)
		}

		(wrong, _) => {
			if let Some(name) = try_name(p)? {
				ast::BlockCompSpec::Block(name)
			} else {
				let sp = p.peek(0).span;
				p.emit(
					DiagBuilder2::error(format!("Expected block name, component label, `all`, or `others`, found {} instead", wrong))
					.span(sp)
				);
				return Err(Reported);
			}
		}
	};

	span.expand(p.last_span());
	Ok(Spanned::new(spec, span))
}


/// Parse a configuration specification. See IEEE 1076-2008 section 7.3.1.
///
/// ```text
/// config_spec := "for" block_comp_spec binding_ind {vunit_binding_ind} ["end" "for" ";"]
/// ```
pub fn parse_config_spec<P: Parser>(p: &mut P) -> ReportedResult<ast::CfgSpec> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::For))?;
	let spec = parse_block_comp_spec(p)?;
	let bind = parse_binding_ind(p)?;
	let vunits = repeat(p, |p| -> ReportedResult<Option<()>> {
		if p.peek(0).value == Keyword(Kw::Use) && p.peek(1).value == Keyword(Kw::Vunit) {
			Ok(Some(parse_vunit_binding_ind(p)?))
		} else {
			Ok(None)
		}
	})?;
	if accept(p, Keyword(Kw::End)) {
		require(p, Keyword(Kw::For))?;
		require(p, Semicolon)?;
	}
	span.expand(p.last_span());
	Ok(ast::CfgSpec{
		span: span,
		spec: spec,
		bind: bind,
		vunits: vunits,
	})
}


/// Parse an attribute declaration or specification. See IEEE 1076-2008 sections
/// 6.7 and 7.2.
///
/// ```text
/// attribute_decl
///   := "attribute" ident ":" name ";"
///   := "attribute" ident "of" ({name [signature]}","+ | "others" | "all") ":" entity_class "is" expr ";"
/// ```
pub fn parse_attr_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::AttrDecl> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Attribute))?;
	let name = parse_ident(p, "attribute name")?;

	// Depending on the next token, parse either a declaration or a
	// specification.
	if accept(p, Colon) {
		let ty = parse_name(p)?;
		require(p, Semicolon)?;
		span.expand(p.last_span());
		Ok(ast::AttrDecl{
			id: Default::default(),
			span: span,
			name: name,
			data: ast::AttrData::Decl(ty),
		})
	} else if accept(p, Keyword(Kw::Of)) {
		// Parse the entity specification.
		let target = match p.peek(0).value {
			Keyword(Kw::Others) => { p.bump(); ast::AttrTarget::Others }
			Keyword(Kw::All) => { p.bump(); ast::AttrTarget::All }
			_ => {
				let l = separated_nonempty(p, Comma, Colon, "name", |p|{
					let name = parse_name(p)?;
					let sig = try_flanked(p, Brack, parse_signature)?;
					Ok((name, sig))
				})?;
				ast::AttrTarget::List(l)
			}
		};

		// Parse the entity class.
		require(p, Colon)?;
		let cls = parse_entity_class(p)?;

		// Parse the rest.
		require(p, Keyword(Kw::Is))?;
		let expr = parse_expr(p)?;
		require(p, Semicolon)?;
		span.expand(p.last_span());
		Ok(ast::AttrDecl{
			id: Default::default(),
			span: span,
			name: name,
			data: ast::AttrData::Spec{
				target: target,
				cls: cls,
				expr: expr,
			}
		})
	} else {
		let pk = p.peek(0);
		p.emit(
			DiagBuilder2::error(format!("Expected `:` or `of` after attribute name, found {} instead", pk.value))
			.span(pk.span)
			.add_note("see IEEE 1076-2008 sections 6.7 and 7.2")
		);
		Err(Reported)
	}
}


/// Parse an entity class. See IEEE 1076-2008 section 7.2.
///
/// ```text
/// entity_class
///   := "entity"
///   := "architecture"
///   := "configuration"
///   := "procedure"
///   := "function"
///   := "package"
///   := "type"
///   := "subtype"
///   := "constant"
///   := "signal"
///   := "variable"
///   := "component"
///   := "label"
///   := "literal"
///   := "units"
///   := "group"
///   := "file"
///   := "property"
///   := "sequence"
/// ```
pub fn parse_entity_class<P: Parser>(p: &mut P) -> ReportedResult<ast::EntityClass> {
	let pk = p.peek(0);
	let cls = match pk.value {
		Keyword(Kw::Architecture)  => ast::EntityClass::Arch,
		Keyword(Kw::Component)     => ast::EntityClass::Comp,
		Keyword(Kw::Configuration) => ast::EntityClass::Cfg,
		Keyword(Kw::Constant)      => ast::EntityClass::Const,
		Keyword(Kw::Entity)        => ast::EntityClass::Entity,
		Keyword(Kw::File)          => ast::EntityClass::File,
		Keyword(Kw::Function)      => ast::EntityClass::Func,
		Keyword(Kw::Group)         => ast::EntityClass::Group,
		Keyword(Kw::Label)         => ast::EntityClass::Label,
		Keyword(Kw::Literal)       => ast::EntityClass::Literal,
		Keyword(Kw::Package)       => ast::EntityClass::Pkg,
		Keyword(Kw::Procedure)     => ast::EntityClass::Proc,
		Keyword(Kw::Property)      => ast::EntityClass::Prop,
		Keyword(Kw::Sequence)      => ast::EntityClass::Seq,
		Keyword(Kw::Signal)        => ast::EntityClass::Signal,
		Keyword(Kw::Subtype)       => ast::EntityClass::Subtype,
		Keyword(Kw::Type)          => ast::EntityClass::Type,
		Keyword(Kw::Units)         => ast::EntityClass::Units,
		Keyword(Kw::Variable)      => ast::EntityClass::Var,
		wrong => {
			p.emit(
				DiagBuilder2::error(format!("Expected entity class, found {} instead", wrong))
				.span(pk.span)
				.add_note("An entity class is any of the keywords `architecture`, `component`, `configuration`, `constant`, `entity`, `file`, `function`, `group`, `label`, `literal`, `package`, `procedure`, `property`, `sequence`, `signal`, `subtype`, `type`, `units`, or `variable`")
				.add_note("see IEEE 1076-2008 section 7.2")
			);
			return Err(Reported);
		}
	};
	p.bump();
	Ok(cls)
}


/// Parse a group declaration or group template declaration. See IEEE 1076-2008
/// sections 6.9 and 6.10.
///
/// ```text
/// group_decl
///   := "group" ident "is" "(" {entity_class ["<>"]}","+ ")" ";"
///   := "group" ident ":" name ";"
/// ```
pub fn parse_group_decl<P: Parser>(p: &mut P) -> ReportedResult<ast::GroupDecl> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Group))?;
	let name = parse_ident(p, "group name")?;

	// Parse either a declaration or template declaration, depending on the next
	// token.
	let data = if accept(p, Colon) {
		let ty = parse_name(p)?;
		ast::GroupData::Decl(ty)
	} else if accept(p, Keyword(Kw::Is)) {
		let elems = flanked(p, Paren, |p| separated_nonempty(
			p, Comma, CloseDelim(Paren), "group element", |p|{
				let cls = parse_entity_class(p)?;
				let open = accept(p, LtGt);
				Ok((cls, open))
			}
		).map_err(|e| e.into()))?;
		ast::GroupData::Temp(elems)
	} else {
		let pk = p.peek(0);
		p.emit(
			DiagBuilder2::error(format!("Expected `:` or `is` after group name, found {} instead", pk.value))
			.span(pk.span)
			.add_note("`group <name> is ...` declares a group template")
			.add_note("`group <name> : ...` declares group")
			.add_note("see IEEE 1076-2008 sections 6.9 and 6.10")
		);
		return Err(Reported);
	};

	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(ast::GroupDecl{
		id: Default::default(),
		span: span,
		name: name,
		data: data,
	})
}


/// Parse a sequential or concurrent statement.
pub fn parse_stmt<P: Parser>(p: &mut P) -> ReportedResult<ast::Stmt> {
	let mut span = p.peek(0).span;

	// Parse the leading statement label, if any.
	let label = try_label(p);

	// Handle the simple cases where the statement is clearly identified and
	// introduced by a keyword. Otherwise try the more complex cases introduced
	// by a name or parenthesized expression (aggregate).
	let data = match p.peek(0).value {
		Keyword(Kw::Wait) => parse_wait_stmt(p)?,
		Keyword(Kw::Assert) => parse_assert_stmt(p)?,
		Keyword(Kw::Report) => parse_report_stmt(p)?,

		// For the if statement, check if the `generate` or the `then` keyword
		// occurs earlier. This allows us to determine whether we should parse a
		// generate or regular statement.
		Keyword(Kw::If) => match earliest(p, &[Keyword(Kw::Generate), Keyword(Kw::Then), Keyword(Kw::End)]).value {
			Keyword(Kw::Generate) => parse_if_generate_stmt(p, label)?,
			_ => parse_if_stmt(p, label)?,
		},

		// For the case statement, check if the `generate` or the `is` keyword
		// occurs earlier. This allows us to determine whether we should parse a
		// generate or regular statement.
		Keyword(Kw::Case) => match earliest(p, &[Keyword(Kw::Generate), Keyword(Kw::Is), Keyword(Kw::End)]).value {
			Keyword(Kw::Generate) => parse_case_generate_stmt(p, label)?,
			_ => parse_case_stmt(p, label)?,
		},

		// For the loop statements, check if the `generate` or the `loop`
		// keyword occurs earlier. This allows us to determine whether we should
		// parse a generate or a regular statement.
		Keyword(Kw::For) => match earliest(p, &[Keyword(Kw::Generate), Keyword(Kw::Loop), Keyword(Kw::End)]).value {
			Keyword(Kw::Generate) => parse_for_generate_stmt(p, label)?,
			_ => parse_loop_stmt(p, label)?,
		},
		Keyword(Kw::While) | Keyword(Kw::Loop) => parse_loop_stmt(p, label)?,

		Keyword(Kw::Next) | Keyword(Kw::Exit) => parse_nexit_stmt(p)?,
		Keyword(Kw::Return) => parse_return_stmt(p)?,
		Keyword(Kw::Null) => parse_null_stmt(p)?,
		Keyword(Kw::Block) => parse_block_stmt(p, label)?,
		Keyword(Kw::Process) => parse_proc_stmt(p, label)?,
		Keyword(Kw::With) => parse_select_assign(p)?,
		Keyword(Kw::Component) | Keyword(Kw::Entity) | Keyword(Kw::Configuration) => {
			let target = match p.peek(0).value {
				Keyword(Kw::Component) => ast::InstTarget::Comp,
				Keyword(Kw::Entity) => ast::InstTarget::Entity,
				Keyword(Kw::Configuration) => ast::InstTarget::Cfg,
				_ => unreachable!(),
			};
			p.bump();
			let name = parse_name(p)?;
			parse_inst_or_call_tail(p, Some(target), name)?
		}

		wrong => {
			if let Some(name) = try_name(p)? {
				// Try to parse a statement that begins with a name.
				match p.peek(0).value {
					Leq | VarAssign => parse_assign_tail(p, ast::AssignTarget::Name(name))?,
					_ => parse_inst_or_call_tail(p, None, name)?,
				}
			} else if let Some(expr) = try_paren_expr(p)? {
				// Try to parse a statement that begins with a parenthesized
				// expression, aka an assignment.
				parse_assign_tail(p, ast::AssignTarget::Aggregate(expr))?
			} else {
				// If we get here, nothing matched, so throw an error.
				let q = p.peek(0).span;
				p.emit(
					DiagBuilder2::error(format!("Expected statement, found {} instead", wrong))
					.span(q)
					.add_note("see IEEE 1076-2008 section 10")
				);
				return Err(Reported);
			}
		}
	};

	span.expand(p.last_span());
	Ok(ast::Stmt{
		id: Default::default(),
		span: span,
		label: label,
		data: data,
	})
}


/// Parse an optional label, which basically is just an identifier followed by
/// a colon. This is interesting for statement parsing. See IEEE 1076-2008
/// section 10.
pub fn try_label<P: Parser>(p: &mut P) -> Option<Spanned<Name>> {
	if let (Spanned{ value: Ident(n), span }, Colon) = (p.peek(0), p.peek(1).value) {
		p.bump();
		p.bump();
		Some(Spanned::new(n, span))
	} else {
		None
	}
}


/// Parse a wait statement. See IEEE 1076-2008 section 10.2.
///
/// ```text
/// wait_stmt := "wait" ["on" {name}","+] ["until" expr] ["for" expr] ";"
/// ```
pub fn parse_wait_stmt<P: Parser>(p: &mut P) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::Wait))?;

	// Parse the optional "on" part.
	let on = if accept(p, Keyword(Kw::On)) {
		let names = separated_nonempty(
			p,
			Comma,
			token_predicate!(Keyword(Kw::Until), Keyword(Kw::For), Semicolon),
			"signal name",
			parse_name
		)?;
		Some(names)
	} else {
		None
	};

	// Parse the optional "until" part.
	let until = if accept(p, Keyword(Kw::Until)) {
		Some(parse_expr(p)?)
	} else {
		None
	};

	// Parse the optional "for" part.
	let time = if accept(p, Keyword(Kw::For)) {
		Some(parse_expr(p)?)
	} else {
		None
	};

	require(p, Semicolon)?;
	Ok(ast::WaitStmt{
		on: on,
		until: until,
		time: time,
	})
}


/// Parse an assertion statement. See IEEE 1076-2008 section 10.3.
///
/// ```text
/// assert_stmt := "assert" expr ["report" expr] ["severity" expr] ";"
/// ```
pub fn parse_assert_stmt<P: Parser>(p: &mut P) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::Assert))?;
	let cond = parse_expr(p)?;

	// Parse the optional "report" part.
	let report = if accept(p, Keyword(Kw::Report)) {
		Some(parse_expr(p)?)
	} else {
		None
	};

	// Parse the optional "severity" part.
	let severity = if accept(p, Keyword(Kw::Severity)) {
		Some(parse_expr(p)?)
	} else {
		None
	};

	require(p, Semicolon)?;
	Ok(ast::AssertStmt{
		cond: cond,
		report: report,
		severity: severity,
	})
}


/// Parse a report statement. See IEEE 1076-2008 section 10.4.
///
/// ```text
/// report_stmt := "report" expr ["severity" expr] ";"
/// ```
pub fn parse_report_stmt<P: Parser>(p: &mut P) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::Report))?;
	let msg = parse_expr(p)?;

	// Parse the optional "severity" part.
	let severity = if accept(p, Keyword(Kw::Severity)) {
		Some(parse_expr(p)?)
	} else {
		None
	};

	require(p, Semicolon)?;
	Ok(ast::ReportStmt{
		msg: msg,
		severity: severity,
	})
}


/// Parse an if statement. See IEEE 1076-2008 section 10.8.
///
/// ```text
/// if_stmt :=
///   "if" expr "then" {stmt}
///   {"elsif" expr "then" {stmt}}
///   ["else" {stmt}]
///   "end" "if" [ident] ";"
/// ```
pub fn parse_if_stmt<P: Parser>(p: &mut P, label: Option<Spanned<Name>>) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::If))?;

	// Parse the first `if` and subsequent `elsif` branches.
	let conds = separated_nonempty(
		p,
		Keyword(Kw::Elsif),
		token_predicate!(Keyword(Kw::Else), Keyword(Kw::End)),
		"if branch",
		|p|{
			let cond = parse_expr(p)?;
			require(p, Keyword(Kw::Then))?;
			let stmts = repeat_until(
				p,
				token_predicate!(Keyword(Kw::Elsif), Keyword(Kw::Else), Keyword(Kw::End)),
				parse_stmt
			)?;
			Ok((cond, ast::StmtBody{
				id: Default::default(),
				stmts: stmts
			}))
		}
	)?;

	// Parse the optional `else` branch.
	let alt = if accept(p, Keyword(Kw::Else)) {
		Some(ast::StmtBody{
			id: Default::default(),
			stmts: repeat_until(p, Keyword(Kw::End), parse_stmt)?,
		})
	} else {
		None
	};

	// Parse the rest.
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::If))?;
	parse_optional_matching_ident(p, label, "if statement", "section 10.8");
	require(p, Semicolon)?;
	Ok(ast::IfStmt{
		conds: conds,
		alt: alt,
	})
}


/// Parse a case statement. See IEEE 1076-2008 section 10.9.
///
/// ```text
/// case_stmt:= "case" ["?"] expr "is" {"when" {expr}"|"+ "=>" {stmt}} "end" "case" ["?"] [ident] ";"
/// ```
pub fn parse_case_stmt<P: Parser>(p: &mut P, label: Option<Spanned<Name>>) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::Case))?;
	let has_qm = accept(p, Qmark);
	let switch = parse_expr(p)?;
	require(p, Keyword(Kw::Is))?;

	// Parse the cases.
	let cases = repeat(p, |p| -> ReportedResult<Option<(_,_)>> {
		if accept(p, Keyword(Kw::When)) {
			let choices = separated_nonempty(p, Pipe, Arrow, "choice", parse_expr)?;
			require(p, Arrow)?;
			let stmts = repeat_until(p, token_predicate!(Keyword(Kw::When), Keyword(Kw::End)), parse_stmt)?;
			Ok(Some((choices, ast::StmtBody{
				id: Default::default(),
				stmts: stmts,
			})))
		} else {
			Ok(None)
		}
	})?;

	// Parse the rest.
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::Case))?;
	let trail_qm = accept(p, Qmark); // TODO: Check if this matches.
	parse_optional_matching_ident(p, label, "case statement", "section 10.9");
	require(p, Semicolon)?;
	Ok(ast::CaseStmt{
		qm: has_qm,
		switch: switch,
		cases: cases,
	})
}


/// Parse a loop statement. See IEEE 1076-2008 section 10.10.
///
/// ```text
/// loop_stmt := ("while" expr | "for" ident "in" expr) "loop" {stmt} "end" "loop" [ident] ";"
/// ```
pub fn parse_loop_stmt<P: Parser>(p: &mut P, label: Option<Spanned<Name>>) -> ReportedResult<ast::StmtData> {
	// Determine the looping scheme.
	let pk = p.peek(0);
	let scheme = match pk.value {
		Keyword(Kw::While) => {
			p.bump();
			let cond = parse_expr(p)?;
			ast::LoopScheme::While(cond)
		}
		Keyword(Kw::For) => {
			p.bump();
			let param = parse_ident(p, "loop parameter name")?;
			require(p, Keyword(Kw::In))?;
			let range = parse_expr(p)?;
			ast::LoopScheme::For(param.into(), range)
		}
		_ => ast::LoopScheme::Loop
	};

	// Parse the rest.
	require(p, Keyword(Kw::Loop))?;
	let stmts = repeat_until(p, Keyword(Kw::End), parse_stmt)?;
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::Loop))?;
	parse_optional_matching_ident(p, label, "loop statement", "section 10.10");
	require(p, Semicolon)?;
	Ok(ast::LoopStmt{
		scheme: scheme,
		body: ast::StmtBody{
			id: Default::default(),
			stmts: stmts,
		},
	})
}


/// Parse a next or exit statement. See IEEE 1076-2008 sections 10.11 and 10.12.
///
/// ```text
/// nexit_stmt := ("next"|"exit") [ident] ["when" expr] ";"
/// ```
pub fn parse_nexit_stmt<P: Parser>(p: &mut P) -> ReportedResult<ast::StmtData> {
	let pk = p.peek(0);
	let mode = match pk.value {
		Keyword(Kw::Next) => { p.bump(); ast::NexitMode::Next }
		Keyword(Kw::Exit) => { p.bump(); ast::NexitMode::Exit }
		_ => {
			p.emit(
				DiagBuilder2::error(format!("Expected `next` or `exit`, found {} instead", pk.value))
				.span(pk.span)
				.add_note("see IEEE 1076-2008 sections 10.11 and 10.12")
			);
			return Err(Reported);
		}
	};
	let target = try_ident(p);
	let cond = if accept(p, Keyword(Kw::When)) {
		Some(parse_expr(p)?)
	} else {
		None
	};
	require(p, Semicolon)?;
	Ok(ast::NexitStmt{
		mode: mode,
		target: target.map(|t| t.into()),
		cond: cond,
	})
}


/// Parse a return statement. See IEEE 1076-2008 section 10.13.
///
/// ```text
/// return_stmt := "return" [expr] ";"
/// ```
pub fn parse_return_stmt<P: Parser>(p: &mut P) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::Return))?;
	let expr = if !accept(p, Semicolon) {
		let e = parse_expr(p)?;
		require(p, Semicolon)?;
		Some(e)
	} else {
		None
	};
	Ok(ast::ReturnStmt(expr))
}


/// Parse a null statement. See IEEE 1076-2008 section 10.14.
///
/// ```text
/// null_stmt := "null" ";"
/// ```
pub fn parse_null_stmt<P: Parser>(p: &mut P) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::Null))?;
	require(p, Semicolon)?;
	Ok(ast::NullStmt)
}


/// Parse a generate if statement. See IEEE 1076-2008 section 11.8.
///
/// ```text
/// generate_if_stmt :=
///   "if" [ident ":"] expr "generate" generate_body
///   {"elsif" [ident ":"] expr "generate" generate_body}
///   ["else" [ident ":"] "generate" generate_body]
///   "end" "generate" [ident] ";"
/// ```
pub fn parse_if_generate_stmt<P: Parser>(p: &mut P, label: Option<Spanned<Name>>) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::If))?;

	// Parse the first `if` and subsequent `elsif` branches.
	let conds = separated_nonempty(
		p,
		Keyword(Kw::Elsif),
		token_predicate!(Keyword(Kw::Else), Keyword(Kw::End)),
		"if generate branch",
		|p|{
			let label = try_label(p);
			let cond = parse_expr(p)?;
			require(p, Keyword(Kw::Generate))?;
			let body = parse_generate_body(p, label, token_predicate!(Keyword(Kw::Elsif), Keyword(Kw::Else), Keyword(Kw::End)))?;
			Ok((cond, body))
		}
	)?;

	// Parse the optional `else` branch.
	let alt = if accept(p, Keyword(Kw::Else)) {
		let label = try_label(p);
		require(p, Keyword(Kw::Generate))?;
		let body = parse_generate_body(p, label, Keyword(Kw::End))?;
		Some(body)
	} else {
		None
	};

	// Parse the rest.
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::Generate))?;
	parse_optional_matching_ident(p, label, "generate statement", "section 11.8");
	require(p, Semicolon)?;
	Ok(ast::IfGenStmt{
		conds: conds,
		alt: alt,
	})
}


/// Parse a generate case statement. See IEEE 1076-2008 section 11.8.
///
/// ```text
/// generate_case_stmt := "case" expr "generate" {"when" [ident ":"] {expr}"|"+ "=>" generate_body}+ "end" "generate" [ident] ";"
/// ```
pub fn parse_case_generate_stmt<P: Parser>(p: &mut P, label: Option<Spanned<Name>>) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::Case))?;
	let switch = parse_expr(p)?;
	require(p, Keyword(Kw::Generate))?;

	// Parse the cases.
	let cases = repeat(p, |p| -> ReportedResult<Option<(Vec<ast::Expr>, ast::GenBody)>> {
		if accept(p, Keyword(Kw::When)) {
			let label = try_label(p);
			let choices = separated_nonempty(p, Pipe, Arrow, "choice", parse_expr)?;
			require(p, Arrow)?;
			let body = parse_generate_body(p, label, token_predicate!(Keyword(Kw::When), Keyword(Kw::End)))?;
			Ok(Some((choices, body)))
		} else {
			Ok(None)
		}
	})?;

	// Parse the rest.
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::Generate))?;
	parse_optional_matching_ident(p, label, "generate statement", "section 11.8");
	require(p, Semicolon)?;
	Ok(ast::CaseGenStmt{
		switch: switch,
		cases: cases,
	})
}


/// Parse a generate for statement. See IEEE 1076-2008 section 11.8.
///
/// ```text
/// generate_for_stmt := "for" ident "in" expr "generate" generate_body "end" "generate" [ident] ";"
/// ```
pub fn parse_for_generate_stmt<P: Parser>(p: &mut P, label: Option<Spanned<Name>>) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::For))?;
	let param = parse_ident(p, "loop parameter name")?;
	require(p, Keyword(Kw::In))?;
	let range = parse_expr(p)?;
	require(p, Keyword(Kw::Generate))?;
	let body = parse_generate_body(p, label, Keyword(Kw::End))?;
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::Generate))?;
	parse_optional_matching_ident(p, label, "generate statement", "section 11.8");
	require(p, Semicolon)?;
	Ok(ast::ForGenStmt{
		param: param.into(),
		range: range,
		body: body,
	})
}


/// Parse a generate body. See IEEE 1076-2008 section 11.8.
///
/// ```text
/// [{decl_item}+ "begin"] {stmt} ["end" [ident] ";"]
/// ```
pub fn parse_generate_body<P: Parser, T>(p: &mut P, label: Option<Spanned<Name>>, term: T) -> ReportedResult<ast::GenBody>
where T: Predicate<P> {
	let mut span = p.peek(0).span;

	// Parse the optional declarative part. Care must be taken when parsing the
	// declarative items, since the `for` and `component` may introduce both a
	// regular statement or a declarative item.
	let decl_items = repeat(p, |p|{
		// Statement introduced by label `ident ":"`.
		if p.peek(0).value.is_ident() && p.peek(1).value == Colon {
			return Ok(None);
		}
		// Component instantiation.
		if p.peek(0).value == Keyword(Kw::Component) && p.peek(2).value != Keyword(Kw::Is) {
			return Ok(None);
		}
		// Configuration specification starting with `for`. Hard to distinguish
		// from a for statement or for generate statement. We use a cue from the
		// structure of the three variants: Statements have a `loop` or
		// `generate` keyword very shortly after `for`, whereas a configuration
		// specification has at least one semicolon before any of these
		// keywords.
		if p.peek(0).value == Keyword(Kw::For) && earliest(p, &[Keyword(Kw::Loop), Keyword(Kw::Generate), Semicolon]).value == Semicolon {
			return Ok(None);
		}

		try_decl_item(p)
	})?;

	// Parse the `begin` that introduces the body. Optional if no declarative
	// items were given.
	let has_begin = accept(p, Keyword(Kw::Begin));
	if !decl_items.is_empty() && !has_begin {
		let pk = p.peek(0);
		p.emit(
			DiagBuilder2::error(format!("`begin` is required before {}, to separate it from the preceding declarative items", pk.value))
			.span(pk.span)
		);
		return Err(Reported);
	}

	// Parse the statements in the body.
	let stmts = repeat_until(
		p,
		term,
		parse_stmt
	)?;

	// Parse the `end` and optional trailing label.
	let has_end = if p.peek(0).value == Keyword(Kw::End) && p.peek(1).value != Keyword(Kw::Generate) {
		p.bump();
		parse_optional_matching_ident(p, label, "generate body", "section 11.8");
		require(p, Semicolon)?;
		true
	} else {
		false
	};

	span.expand(p.last_span());
	Ok(ast::GenBody{
		id: Default::default(),
		label: label,
		span: span,
		decls: decl_items,
		stmts: stmts,
	})
}


/// Parse a block statement. See IEEE 1076-2008 section 11.2.
///
/// ```text
/// block_stmt := "block" ["(" expr ")"] ["is"] {decl_item} "begin" {stmt} "end" "block" [ident] ";"
/// ```
pub fn parse_block_stmt<P: Parser>(p: &mut P, label: Option<Spanned<Name>>) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::Block))?;
	let guard = try_flanked(p, Paren, parse_expr)?;
	accept(p, Keyword(Kw::Is));
	let decl_items = repeat(p, try_decl_item)?;
	require(p, Keyword(Kw::Begin))?;
	let stmts = repeat_until(p, Keyword(Kw::End), parse_stmt)?;
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::Block))?;
	parse_optional_matching_ident(p, label, "block", "section 11.2");
	require(p, Semicolon)?;
	Ok(ast::BlockStmt{
		guard: guard,
		decls: decl_items,
		stmts: stmts,
	})
}


/// Parse a process statement. See IEEE 1076-2008 section 11.3.
///
/// ```text
/// process_stmt := "process" ["(" ("all"|{name}",") ")"] ["is"] {decl_item} "begin" {stmt} "end" ["postponed"] "process" [ident] ";"
/// ```
pub fn parse_proc_stmt<P: Parser>(p: &mut P, label: Option<Spanned<Name>>) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::Process))?;

	// Parse the optional sensitivity list.
	let sensitivity = try_flanked(p, Paren, |p|{
		if accept(p, Keyword(Kw::All)) {
			Ok(ast::Sensitivity::All)
		} else {
			let l = separated(p, Comma, CloseDelim(Paren), "signal name", parse_name)?;
			Ok(ast::Sensitivity::List(l))
		}
	})?;
	accept(p, Keyword(Kw::Is));

	// Parse the declarative part.
	let decl_items = repeat(p, try_decl_item)?;

	// Parse the statement body.
	require(p, Keyword(Kw::Begin))?;
	let stmts = repeat_until(p, Keyword(Kw::End), parse_stmt)?;
	require(p, Keyword(Kw::End))?;

	// Parse the rest.
	let postponed = accept(p, Keyword(Kw::Postponed));
	require(p, Keyword(Kw::Process))?;
	parse_optional_matching_ident(p, label, "process", "section 11.3");
	require(p, Semicolon)?;
	Ok(ast::ProcStmt{
		sensitivity: sensitivity,
		decls: decl_items,
		stmts: stmts,
		postponed: postponed,
	})
}


/// Parse the tail of an assign statement. This function assumes that the name
/// of the signal to be assigned has already been parsed. See IEEE 1076-2008
/// section 10.5.
///
/// ```text
/// assign_stmt
///   := assign_dst "release" [force_mode] ";"
///   := assign_dst assign_mode cond_waves ";"
/// assign_dst := (name|paren_expr) . ("<=" | ":=") ["guarded"]
/// assign_mode := [delay_mech] | "force" [force_mode]
///
/// force_mode := "in" | "out"
/// delay_mech := "transport" | ["reject" expr] "inertial"
/// ```
pub fn parse_assign_tail<P: Parser>(p: &mut P, target: ast::AssignTarget) -> ReportedResult<ast::StmtData> {
	let (kind, guarded) = parse_assign_dst_tail(p)?;
	let mode = match p.peek(0).value {
		Keyword(Kw::Release) => {
			p.bump();
			let fm = try_force_mode(p);
			ast::AssignMode::Release(fm)
		}

		Keyword(Kw::Force) => {
			p.bump();
			let fm = try_force_mode(p);
			let waves = parse_cond_waves(p)?;
			ast::AssignMode::Force(fm, waves)
		}

		_ => {
			let dm = try_delay_mech(p)?;
			let waves = parse_cond_waves(p)?;
			ast::AssignMode::Normal(dm, waves)
		}
	};
	require(p, Semicolon)?;
	Ok(ast::AssignStmt{
		target: target,
		kind: kind,
		guarded: guarded,
		mode: mode,
	})
}


/// Parse a select assign statement. See IEEE 1076-2008 section 10.5.
///
/// ```text
/// assign_stmt := "with" expr "select" ["?"] assign_dst assign_mode selected_waves ";"
/// assign_dst  := (name|paren_expr) ("<=" | ":=") ["guarded"]
/// assign_mode := [delay_mech] | "force" [force_mode]
///
/// force_mode := "in" | "out"
/// delay_mech := "transport" | ["reject" expr] "inertial"
/// ```
pub fn parse_select_assign<P: Parser>(p: &mut P) -> ReportedResult<ast::StmtData> {
	require(p, Keyword(Kw::With))?;
	let select = parse_expr(p)?;
	require(p, Keyword(Kw::Select))?;
	let qm = accept(p, Qmark);

	// Parse the assignment target, which is either a signal name or an
	// aggregate.
	let target = if let Some(name) = try_name(p)? {
		ast::AssignTarget::Name(name)
	} else if let Some(exprs) = try_paren_expr(p)? {
		ast::AssignTarget::Aggregate(exprs)
	} else {
		let pk = p.peek(0);
		p.emit(
			DiagBuilder2::error(format!("Expected signal name, variable name or aggregate, found {} instead", pk.value))
			.span(pk.span)
			.add_note("see IEEE 1076-2008 section 10.5")
		);
		return Err(Reported);
	};

	// Parse the rest of the destination.
	let (kind, guarded) = parse_assign_dst_tail(p)?;

	// Parse the assignment mode and rest of the statement.
	let (mode, waves) = match p.peek(0).value {
		Keyword(Kw::Force) => {
			p.bump();
			let fm = try_force_mode(p);
			let waves = parse_selected_waves(p)?;
			(ast::SelectAssignMode::Force(fm), waves)
		}

		_ => {
			let dm = try_delay_mech(p)?;
			let waves = parse_selected_waves(p)?;
			(ast::SelectAssignMode::Normal(dm), waves)
		}
	};
	require(p, Semicolon)?;
	Ok(ast::SelectAssignStmt{
		select: select,
		qm: qm,
		target: target,
		kind: kind,
		guarded: guarded,
		mode: mode,
		waves: waves,
	})
}


pub fn parse_assign_dst_tail<P: Parser>(p: &mut P) -> ReportedResult<(ast::AssignKind, bool)> {
	let pk = p.peek(0);
	let kind = match pk.value {
		Leq => ast::AssignKind::Signal,
		VarAssign => ast::AssignKind::Var,
		_ => {
			p.emit(
				DiagBuilder2::error(format!("Expected `<=` or `:=` after assignment target, found {} instead", pk.value))
				.span(pk.span)
				.add_note("see IEEE 1076-2008 section 10.5")
			);
			return Err(Reported);
		}
	};
	p.bump();
	let guarded = accept(p, Keyword(Kw::Guarded));
	Ok((kind, guarded))
}


pub fn try_force_mode<P: Parser>(p: &mut P) -> Option<Spanned<ast::ForceMode>> {
	if let Some(m) = match p.peek(0).value {
		Keyword(Kw::In)  => Some(ast::ForceMode::In),
		Keyword(Kw::Out) => Some(ast::ForceMode::Out),
		_ => None
	}{
		p.bump();
		Some(Spanned::new(m, p.last_span()))
	} else {
		None
	}
}


/// Try to parse a delay mechanism.
///
/// ```text
/// "transport" | ["reject" expr] "inertial"
/// ```
pub fn try_delay_mech<P: Parser>(p: &mut P) -> ReportedResult<Option<Spanned<ast::DelayMech>>> {
	Ok(match p.peek(0).value {
		Keyword(Kw::Transport) => {
			p.bump();
			Some(Spanned::new(ast::DelayMech::Transport, p.last_span()))
		}
		Keyword(Kw::Inertial) => {
			p.bump();
			Some(Spanned::new(ast::DelayMech::Inertial, p.last_span()))
		}
		Keyword(Kw::Reject) => {
			p.bump();
			let sp = p.last_span();
			let expr = parse_expr(p)?;
			require(p, Keyword(Kw::Inertial))?;
			Some(Spanned::new(ast::DelayMech::InertialReject(expr), sp))
		}
		_ => return Ok(None),
	})
}


/// Parse a list of conditional waveforms. See IEEE 1076-2008 section 10.5.
///
/// ```text
/// cond_waves := { wave ["when" expr] }"else"+
/// ```
pub fn parse_cond_waves<P: Parser>(p: &mut P) -> ReportedResult<Vec<ast::CondWave>> {
	separated_nonempty(p, Keyword(Kw::Else), Semicolon, "waveform", |p|{
		let wave = parse_wave(p)?;
		let cond = if accept(p, Keyword(Kw::When)) {
			Some(parse_expr(p)?)
		} else {
			None
		};
		Ok(ast::CondWave(wave, cond))
	}).map_err(|e| e.into())
}


/// Parse a list of selected waveforms. See IEEE 1076-2008 section 10.5.
///
/// ```text
/// selected_waves := { wave "when" {expr}"|"+ }","+
/// ```
pub fn parse_selected_waves<P: Parser>(p: &mut P) -> ReportedResult<Vec<ast::SelectWave>> {
	separated_nonempty(p, Comma, Semicolon, "waveform", |p|{
		let wave = parse_wave(p)?;
		require(p, Keyword(Kw::When))?;
		let choices = separated_nonempty(p, Pipe, token_predicate!(Comma, Semicolon), "choice", parse_expr)?;
		Ok(ast::SelectWave(wave, choices))
	}).map_err(|e| e.into())
}


/// Parse a waveform. See IEEE 1076-2008 section 10.5.
///
/// ```text
/// wave := {expr ["after" expr]}","+ | "unaffected"
/// ```
pub fn parse_wave<P: Parser>(p: &mut P) -> ReportedResult<ast::Wave> {
	let mut span = p.peek(0).span;
	let elems = if accept(p, Keyword(Kw::Unaffected)) {
		None
	} else {
		Some(separated(p, Comma, token_predicate!(Keyword(Kw::When), Semicolon), "waveform element", |p|{
			let expr = parse_expr(p)?;
			let delay = if accept(p, Keyword(Kw::After)) {
				Some(parse_expr(p)?)
			} else {
				None
			};
			Ok((expr, delay))
		})?)
	};
	span.expand(p.last_span());
	Ok(ast::Wave{
		span: span,
		elems: elems,
	})
}


/// Parse the tail of an instantiation or procedure call statement. See IEEE
/// 1076-2008 sections 10.7, 11.4, and 11.7.
///
/// ```text
/// ["component"|"entity"|"configuration"] name . [generic_map_aspect] [port_map_aspect] ";"
/// ```
pub fn parse_inst_or_call_tail<P: Parser>(p: &mut P, target: Option<ast::InstTarget>, name: ast::CompoundName) -> ReportedResult<ast::StmtData> {
	let gm = try_map_aspect(p, Kw::Generic)?;
	let pm = try_map_aspect(p, Kw::Port)?;
	require(p, Semicolon)?;
	Ok(ast::InstOrCallStmt{
		target: target,
		name: name,
		generics: gm,
		ports: pm,
	})
}
