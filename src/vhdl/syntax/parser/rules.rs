// Copyright (c) 2017 Fabian Schuiki

//! This module implements a first stage recursive descent parser for VHDL. It
//! can process a stream of input tokens into the coarse, generalized abstract
//! syntax tree defined in [`ast`]. The grammar productions/rules outlined in
//! the VHDL standard are collapsed into more general rules as outlined in the
//! following table.
//!
//! | VHDL Standard                        | Generalized to       |
//! |--------------------------------------|----------------------|
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
use syntax::lexer::token::*;
use syntax::parser::TokenStream;
use syntax::parser::core::*;
use syntax::ast;

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
pub fn parse_design_file<P: Parser>(p: &mut P) {
	let mut units = Vec::new();
	while !p.is_fatal() && p.peek(0).value != Eof {
		match parse_design_unit(p) {
			Ok(unit) => units.push(unit),
			Err(Recovered) => ()
		}
	}
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
pub fn parse_design_unit<P: Parser>(p: &mut P) -> RecoveredResult<()> {
	let context = repeat(p, parse_context_item)?;
	let Spanned{ value: tkn, span: sp } = p.peek(0);
	match match tkn {
		Keyword(Kw::Entity) => parse_entity_decl(p),
		Keyword(Kw::Configuration) => parse_config_decl(p),
		Keyword(Kw::Package) => {
			if p.peek(1).value == Keyword(Kw::Body) {
				parse_package_body(p)
			} else {
				parse_package_decl(p)
			}
		}
		Keyword(Kw::Context) => parse_context_decl(p),
		Keyword(Kw::Architecture) => parse_arch_body(p),
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
		Ok(x) => Ok(x),
		Err(Reported) => {
			recover(p, &[Keyword(Kw::End)], true);
			recover(p, &[Semicolon], true);
			Err(Recovered)
		}
	}
}


/// Parse a context item. IEEE 1076-2008 section 13.4.
///
/// ```text
/// context_item := library_clause | use_clause | context_ref
/// ```
pub fn parse_context_item<P: Parser>(p: &mut P) -> RecoveredResult<Option<()>> {
	recovered(p, &[Semicolon], true, |p|{
		let tkn = p.peek(0).value;
		Ok(match tkn {
			Keyword(Kw::Library) => Some(parse_library_clause(p)?),
			Keyword(Kw::Use) => Some(parse_use_clause(p)?),
			Keyword(Kw::Context) => {
				if p.peek(2).value != Keyword(Kw::Is) {
					Some(parse_context_ref(p)?)
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
pub fn parse_library_clause<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Library))?;
	let names = separated_nonempty(p, Comma, Semicolon, "library name", |p| parse_ident(p, "library name"))?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


/// Parse a use clause. IEEE 1076-2008 section 12.4.
///
/// ```text
/// use_clause := "use" {name}","+
/// ```
pub fn parse_use_clause<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Use))?;
	let names = separated_nonempty(p, Comma, Semicolon, "selected name", parse_name)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


pub fn parse_context_ref<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Context))?;
	let names = separated_nonempty(p, Comma, Semicolon, "selected name", parse_name)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
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

	// Try to parse an attribute name.
	if p.peek(0).value == OpenDelim(Brack) || (p.peek(0).value == Apostrophe && p.peek(1).value.is_ident()) {
		// Parse the optional signature.
		let sig = try_flanked(p, Brack, parse_signature)?;

		// Consume the apostrophe and attribute name.
		require(p, Apostrophe)?;
		let attr = parse_ident(p, "attribute name")?;

		// Extend the name.
		name.span.expand(p.last_span());
		name.parts.push(ast::NamePart::Attribute(attr, None));
		return parse_name_suffix(p, name);
	}

	// Try to parse a function call, slice name, or indexed name.
	if let Some(al) = try_flanked(p, Paren, parse_paren_expr)? {
		name.span.expand(p.last_span());
		name.parts.push(ast::NamePart::Call(ast::AssocList));
		return parse_name_suffix(p, name);
	}

	// Try to parse a range constraint.
	if accept(p, Keyword(Kw::Range)) {
		let expr = parse_expr_prec(p, ExprPrec::Range)?;
		// name.part.push(ast::NamePart::Range);
		name.span.expand(p.last_span());
		return parse_name_suffix(p, name);
	}

	// If we arrive here, none of the suffices matched, and we simply return the
	// prefix that we have received.
	Ok(name)
}


/// Parse the optional trailing name after an entity, configuration, etc., which
/// must match the name at the beginning of the declaration.
fn parse_optional_matching_ident<P,M1,M2>(p: &mut P, name: Spanned<Name>, msg: M1, sec: M2)
where P: Parser, M1: Display, M2: Display {
	match try_ident(p) {
		Some(n) if n.value != name.value => {
			p.emit(
				DiagBuilder2::warning(format!("`{}` does not match the {}'s name `{}`", n.value, msg, name.value))
				.span(n.span)
				.add_note(format!("see IEEE 1076-2008 {}", sec))
			);
		}
		_ => ()
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
pub fn parse_context_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Context))?;
	let name = parse_ident(p, "context name")?;
	require(p, Keyword(Kw::Is))?;
	let clauses = repeat(p, parse_context_item)?;
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Context));
	parse_optional_matching_ident(p, name, "context", "section 13.3");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


/// Parse an entity declaration. See IEEE 1076-2008 section 3.2.
///
/// ```text
/// entity_decl :=
///   "entity" ident "is"
///     entity_header
///     entity_decl_part
///   ["begin" entity_stmt_part]
///   "end" ["entity"] [ident] ";"
/// ```
pub fn parse_entity_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;

	// Parse the head of the declaration.
	require(p, Keyword(Kw::Entity))?;
	let name = parse_ident(p, "entity name")?;
	require(p, Keyword(Kw::Is))?;

	// Parse the declarative part.
	repeat(p, try_decl_item)?;

	// Parse the optional statement part.
	if accept(p, Keyword(Kw::Begin)) {
		// TODO
	}

	// Parse the tail of the declaration.
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Entity));
	parse_optional_matching_ident(p, name, "entity", "section 3.2.1");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


/// Parse a configuration declaration. See IEEE 1076-2008 section 3.4.
///
/// ```text
/// config_decl :=
///   "configuration" ident "of" name "is"
///     {config_decl_item}
///   "end" ["configuration"] [ident] ";"
/// ```
pub fn parse_config_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
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
	Ok(())
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
pub fn parse_arch_body<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;

	// Parse the head of the body.
	require(p, Keyword(Kw::Architecture))?;
	let name = parse_ident(p, "architecture name")?;
	require(p, Keyword(Kw::Of))?;
	let entity = parse_name(p)?;
	require(p, Keyword(Kw::Is))?;

	// Parse the declarative and statement parts.
	let decl_items = repeat(p, try_decl_item)?;
	require(p, Keyword(Kw::Begin))?;
	repeat_until(p, Keyword(Kw::End), parse_stmt)?;

	// Parse the tail of the body.
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Architecture));
	parse_optional_matching_ident(p, name, "architecture", "section 3.3");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


/// Try to parse a generic clause. See IEEE 1076-2008 section 6.5.6.2.
///
/// ```text
/// generic_clause := "generic" "clause" "(" {intf_decl}";"+ ")" ";"
/// ```
pub fn try_generic_clause<P: Parser>(p: &mut P) -> ReportedResult<Option<Vec<()>>> {
	if p.peek(0).value == Keyword(Kw::Generic) && p.peek(1).value != Keyword(Kw::Map) {
		p.bump();
		let i = flanked(p, Paren, |p|{
			Ok(separated_nonempty(p,
				Semicolon,
				CloseDelim(Paren),
				"generic interface declaration",
				|p| parse_intf_decl(p, Some(IntfObjectKind::Constant))
			)?)
		})?;
		require(p, Semicolon)?;
		Ok(Some(i))
	} else {
		Ok(None)
	}
}


/// Try to parse a port clause. See IEEE 1076-2008 section 6.5.6.3.
///
/// ```text
/// port_clause := "port" "clause" "(" {intf_decl}";"+ ")" ";"
/// ```
pub fn try_port_clause<P: Parser>(p: &mut P) -> ReportedResult<Option<Vec<()>>> {
	if p.peek(0).value == Keyword(Kw::Port) && p.peek(1).value != Keyword(Kw::Map) {
		p.bump();
		let i = flanked(p, Paren, |p|{
			Ok(separated_nonempty(p,
				Semicolon,
				CloseDelim(Paren),
				"port interface declaration",
				|p| parse_intf_decl(p, Some(IntfObjectKind::Signal))
			)?)
		})?;
		require(p, Semicolon)?;
		Ok(Some(i))
	} else {
		Ok(None)
	}
}


/// Parse an interface declaration. These are generally part of an interface
/// list as they appear in generic and port clauses within for example entity
/// declarations. See IEEE 1076-2008 section 6.5.1.
pub fn parse_intf_decl<P: Parser>(p: &mut P, default: Option<IntfObjectKind>) -> ReportedResult<()> {
	let Spanned{ value: tkn, mut span } = p.peek(0);
	let kind = match tkn {
		// Try to short-circuit a type interface declarations.
		Keyword(Kw::Type) => {
			parse_type_decl(p, false)?;
			return Ok(());
		}

		// Try to short-circuit a subprogram interface declaration.
		Keyword(Kw::Pure) |
		Keyword(Kw::Impure) |
		Keyword(Kw::Procedure) |
		Keyword(Kw::Function) => {
			let spec = parse_subprog_spec(p)?;
			let default = if accept(p, Keyword(Kw::Is)) {
				if accept(p, LtGt) {
					// subprog_spec "is" "<>"
					Some(())
				} else if let Some(name) = try_name(p)? {
					// subprog_spec "is" name
					Some(())
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
			return Ok(());
		}

		// Try to short-circuit a package interface declaration.
		Keyword(Kw::Package) => {
			let inst = parse_package_inst(p, false)?;
			span.expand(p.last_span());
			return Ok(());
		}

		// Try to parse one of the object declarations.
		Keyword(Kw::Constant) => { p.bump(); IntfObjectKind::Constant }
		Keyword(Kw::Signal)   => { p.bump(); IntfObjectKind::Signal }
		Keyword(Kw::Variable) => { p.bump(); IntfObjectKind::Variable }
		Keyword(Kw::File)     => { p.bump(); IntfObjectKind::File }
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

	// Parse the mode and default to `in` if none is given.
	let mode = match p.peek(0).value {
		Keyword(Kw::In) => { p.bump(); () },
		Keyword(Kw::Out) => { p.bump(); () },
		Keyword(Kw::Inout) => { p.bump(); () },
		Keyword(Kw::Buffer) => { p.bump(); () },
		Keyword(Kw::Linkage) => { p.bump(); () },
		_ => (),
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
	Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntfObjectKind {
	Constant,
	Signal,
	Variable,
	File,
}


/// Try to parse a declarative item. See IEEE 1076-2008 section 3.2.3.
pub fn try_decl_item<P: Parser>(p: &mut P) -> ReportedResult<Option<()>> {
	Ok(match p.peek(0).value {
		// package_decl := "package" ident "is" ...
		// package_body := "package" "body" ident "is" ...
		// package_inst := "package" ident "is" "new" ...
		Keyword(Kw::Package) => {
			if p.peek(1).value == Keyword(Kw::Body) {
				Some(parse_package_body(p)?)
			} else if p.peek(2).value == Keyword(Kw::Is) && p.peek(3).value == Keyword(Kw::New) {
				Some(parse_package_inst(p, true)?)
			} else {
				Some(parse_package_decl(p)?)
			}
		}
		// type_decl := "type" ...
		Keyword(Kw::Type) => Some(parse_type_decl(p, true)?),
		// subtype_decl := "subtype" ...
		Keyword(Kw::Subtype) => Some(parse_subtype_decl(p)?),
		// constant_decl := "constant" ...
		// signal_decl   := "signal" ...
		// variable_decl := ("variable"|"shared") ...
		// file_decl     := "file" ...
		Keyword(Kw::Constant) |
		Keyword(Kw::Signal) |
		Keyword(Kw::Variable) |
		Keyword(Kw::Shared) |
		Keyword(Kw::File) => Some(parse_object_decl(p)?),
		// alias_decl := "alias" ...
		Keyword(Kw::Alias) => Some(parse_alias_decl(p)?),
		// use_clause := "use" ...
		Keyword(Kw::Use) => Some(parse_use_clause(p)?),
		// subprog_spec := "pure"|"impure"|"procedure"|"function" ...
		Keyword(Kw::Pure) |
		Keyword(Kw::Impure) |
		Keyword(Kw::Procedure) |
		Keyword(Kw::Function) => Some(parse_subprog_decl_item(p)?),
		// component_decl := "component" ...
		Keyword(Kw::Component) => Some(parse_component_decl(p)?),
		// discon_spec := "disconnect" ...
		Keyword(Kw::Disconnect) => Some(parse_discon_spec(p)?),
		// config_spec := "for" ...
		Keyword(Kw::For) => Some(parse_config_spec(p)?),
		// attr_decl := "attribute" ...
		Keyword(Kw::Attribute) => Some(parse_attr_decl(p)?),
		// generic_clause     := "generic" ...
		// generic_map_aspect := "generic" "map" ...
		Keyword(Kw::Generic) => {
			if p.peek(1).value == Keyword(Kw::Map) {
				let a = try_map_aspect(p, Kw::Generic)?.unwrap();
				require(p, Semicolon)?;
				Some(a)
			} else {
				Some({ try_generic_clause(p)?.unwrap(); () })
			}
		}
		// port_clause     := "port" ...
		// port_map_aspect := "port" "map" ...
		Keyword(Kw::Port) => {
			if p.peek(1).value == Keyword(Kw::Map) {
				let a = try_map_aspect(p, Kw::Port)?.unwrap();
				require(p, Semicolon)?;
				Some(a)
			} else {
				Some({ try_port_clause(p)?.unwrap(); () })
			}
		}
		// group_decl := "group" ...
		Keyword(Kw::Group) => Some(parse_group_decl(p)?),
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
pub fn parse_subprog_decl_item<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	let spec = parse_subprog_spec(p)?;

	// Try to parse a subprogram declaration.
	if accept(p, Semicolon) {
		span.expand(p.last_span());
		return Ok(());
	}

	// Try to parse a subprogram body or instantiation.
	if accept(p, Keyword(Kw::Is)) {
		// Try to parse a subprogram instantiation. Otherwise fall back to a
		// subprogram body.
		if accept(p, Keyword(Kw::New)) {
			let name = parse_name(p)?;
			let sig = try_flanked(p, Brack, parse_signature)?;
			let gm = try_map_aspect(p, Kw::Generic)?;
			require(p, Semicolon)?;
			return Ok(());
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
			return Ok(());
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
pub fn parse_subtype_ind<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let Spanned{ value: tkn, mut span } = p.peek(0);

	// Try to determine if the subtype indication starts out with a resolution
	// indication. This might either be another name in front of the subtype
	// name, or a element resolution in parenthesis.
	let (res, name) = if let Some(res) = try_flanked(p, Paren, parse_paren_expr)? {
		let name = parse_name(p)?;
		(Some(()/*res*/), name)
	} else {
		let name = parse_name(p)?;
		if let Some(other) = try_name(p)? {
			(Some(()/*name*/), other)
		} else {
			(None, name)
		}
	};

	span.expand(p.last_span());
	Ok(())
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
pub fn parse_paren_expr<P: Parser>(p: &mut P) -> ReportedResult<Vec<Spanned<()>>> {
	separated(p, Comma, CloseDelim(Paren), "expression", |p|{
		// Parse a list of choices, i.e. expressions separated by `|`.
		let mut choices = separated_nonempty(p, Pipe, token_predicate!(Arrow, Comma, CloseDelim(Paren)), "expression", parse_expr)?;

		// If the expressions are followed by a "=>", what we have parsed is a
		// list of choices. Otherwise, ensure that there is only one expression
		// in the list.
		if accept(p, Arrow) {
			let q = p.last_span();
			let actual = parse_expr(p)?;
			Ok(Spanned::new((), Span::union(choices[0].span, actual.span)))
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

			Ok(Spanned::new((), first.span))
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
	match tkn {
		Keyword(Kw::Null) => { p.bump(); return Ok(ast::Expr{ span: span }); },
		Keyword(Kw::Open) => { p.bump(); return Ok(ast::Expr{ span: span }); },
		Keyword(Kw::Others) => { p.bump(); return Ok(ast::Expr{ span: span }); },
		Keyword(Kw::Default) => { p.bump(); return Ok(ast::Expr{ span: span }); },
		LtGt => { p.bump(); return Ok(ast::Expr{ span: span }); },

		Keyword(Kw::New) => {
			p.bump();

			// Try to parse a name or qualified expression.
			if let Some(expr) = try_name_or_qualified_primary_expr(p)? {
				return Ok(expr);
			}

			// Try to parse a name prefixed by parenthesis.
			if let Some(paren) = try_flanked(p, Paren, parse_paren_expr)? {
				let name = parse_name(p)?;
				span.expand(p.last_span());
				return Ok(ast::Expr{ span: span });
			}

			// Throw an error.
			p.emit(
				DiagBuilder2::error("Expected subtype or qualified expression after `new`")
				.span(span)
			);
			return Err(Reported);
		}

		Lit(Literal::Abstract(_, _, _, _)) => {
			p.bump();

			// Try to parse a name, which indicates that this abstract literal
			// is part of a physical literal with a unit.
			if let Some(unit) = try_name(p)? {
				span.expand(p.last_span());
				return Ok(ast::Expr{ span: span });
			}

			return Ok(ast::Expr{ span: span });
		}

		Lit(Literal::BitString(_, _, _)) => {
			p.bump();
			return Ok(ast::Expr{ span: span });
		}

		OpenDelim(Paren) => {
			let expr = flanked(p, Paren, parse_paren_expr)?;

			// Try to parse a name, which caters for the case of subtype
			// indications that are prefixed with element resolution.
			if let Some(resol) = try_name(p)? {
				span.expand(p.last_span());
				return Ok(ast::Expr{ span: span });
			}

			span.expand(p.last_span());
			return Ok(ast::Expr{ span: span });
		}

		_ => ()
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
			return Ok(Some(ast::Expr{ span: span }));
		}

		// Try to parse a `'`, which would make this a qualified expression.
		if accept(p, Apostrophe) {
			if p.peek(0).value == OpenDelim(Paren) {
				let expr = flanked(p, Paren, parse_paren_expr)?;
				return Ok(Some(ast::Expr{ span: span }));
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

		return Ok(Some(ast::Expr{ span: span }));
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

	// Try to parse a binary operator.
	if let Some(op) = as_unary_op(tkn) {
		let op_prec = unary_prec(op);
		if prec <= op_prec {
			p.bump();
			let rhs = parse_expr_prec(p, op_prec)?;
			span.expand(p.last_span());
			return parse_expr_suffix(p, ast::Expr{ span: span }, prec);
		}
	}

	// Parse a primary expression.
	let primary = parse_primary_expr(p)?;

	// Parse any optional expression suffix.
	parse_expr_suffix(p, primary, prec)
}


pub fn parse_expr_suffix<P: Parser>(p: &mut P, prefix: ast::Expr, prec: ExprPrec) -> ReportedResult<ast::Expr> {
	let Spanned{ value: tkn, mut span } = p.peek(0);

	// Try to parse a binary operation.
	if let Some(op) = as_binary_op(tkn) {
		let op_prec = binary_prec(op);
		if prec <= op_prec {
			p.bump();
			let expr = parse_expr_prec(p, op_prec)?;
			span.expand(p.last_span());
			return parse_expr_suffix(p, ast::Expr{ span: span }, prec);
		}
	}

	// If we arrive here, none of the suffices matched, so we simply return the
	// expression that we have received.
	Ok(prefix)
}


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
pub fn parse_package_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;

	// Parse the head of the declaration.
	require(p, Keyword(Kw::Package))?;
	let name = parse_ident(p, "package name")?;
	require(p, Keyword(Kw::Is))?;

	// Parse the declarative part.
	repeat(p, try_decl_item)?;

	// Parse the tail of the declaration.
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Package));
	parse_optional_matching_ident(p, name, "package", "section 4.7");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


/// Parse a package body. See IEEE 1076-2008 section 4.8.
///
/// ```text
/// package_decl :=
///   "package" "body" ident "is"
///     {decl_item}
///   "end" ["package" "body"] [ident] ";"
/// ```
pub fn parse_package_body<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Package))?;
	require(p, Keyword(Kw::Body))?;
	let name = parse_ident(p, "package name")?;
	require(p, Keyword(Kw::Is))?;
	repeat(p, try_decl_item)?;
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Package)); // TODO: add proper warnings if these are missing
	accept(p, Keyword(Kw::Body)); // TODO: add proper warnings if these are missing
	parse_optional_matching_ident(p, name, "package body", "section 4.8");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


/// Parse a package instantiation declaration. See IEEE 1076-2008 section 4.9.
///
/// ```text
/// package_inst := "package" ident "is" "new" name [generic_map] ";"
/// ```
pub fn parse_package_inst<P: Parser>(p: &mut P, with_semicolon: bool) -> ReportedResult<()> {
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
	Ok(())
}


/// Try to parse a generic or port map aspect. See IEEE 1076-2008 sections
/// 6.5.7.2 and 6.5.7.3.
///
/// ```text
/// map_aspect := ["generic"|"port"] "map" paren_expr
/// ```
pub fn try_map_aspect<P: Parser>(p: &mut P, kw: Kw) -> ReportedResult<Option<()>> {
	if p.peek(0).value == Keyword(kw) && p.peek(1).value == Keyword(Kw::Map) {
		p.bump();
		p.bump();
		let v = flanked(p, Paren, parse_paren_expr)?;
		Ok(Some(()))
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
pub fn parse_type_decl<P: Parser>(p: &mut P, with_semicolon: bool) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Type))?;
	let name = parse_ident(p, "type name")?;

	// Parse the optional type definition. If present, this is a full type
	// declaration. Otherwise it is an incomplete type declaration.
	if accept(p, Keyword(Kw::Is)) {
		let Spanned{ value: tkn, span: sp } = p.peek(0);
		match tkn {
			// Enumeration type definition
			OpenDelim(Paren) => { flanked(p, Paren, parse_paren_expr)?; },

			// Integer, float, physical type definition
			Keyword(Kw::Range) => {
				p.bump();
				let range = parse_expr(p)?;
				let units = if accept(p, Keyword(Kw::Units)) {
					let u = repeat_until(p, Keyword(Kw::End), |p|{
						let name = parse_ident(p, "unit name")?;
						let rel = if accept(p, Eq) {
							Some(parse_expr(p)?)
						} else {
							None
						};
						require(p, Semicolon)?;
						Ok((name, rel))
					})?;
					require(p, Keyword(Kw::End))?;
					require(p, Keyword(Kw::Units))?;
					parse_optional_matching_ident(p, name, "type", "section 5.2.4");
					Some(u)
				} else {
					None
				};
			}

			// Array type definition
			Keyword(Kw::Array) => {
				p.bump();
				let indices = flanked(p, Paren, parse_paren_expr)?;
				require(p, Keyword(Kw::Of))?;
				let subtype = parse_subtype_ind(p)?;
			}

			// Record type definition
			Keyword(Kw::Record) => {
				p.bump();
				let fields = repeat_until(p, Keyword(Kw::End), |p|{
					let names = separated_nonempty(p,
						Comma,
						Colon,
						"field name",
						|p| parse_ident(p, "field name")
					)?;
					require(p, Colon)?;
					let subtype = parse_subtype_ind(p)?;
					require(p, Semicolon)?;
					Ok((names, subtype))
				})?;
				require(p, Keyword(Kw::End))?;
				require(p, Keyword(Kw::Record))?;
				parse_optional_matching_ident(p, name, "type", "section 5.3.3");
			}

			// Access type definition
			Keyword(Kw::Access) => {
				p.bump();
				let subtype = parse_subtype_ind(p)?;
			}

			// File type definition
			Keyword(Kw::File) => {
				p.bump();
				require(p, Keyword(Kw::Of))?;
				let ty = parse_name(p)?;
			}

			// Protected type declaration and body
			Keyword(Kw::Protected) => { parse_protected_type_def(p, name)?; }

			// Emit an error for anything else.
			wrong => {
				p.emit(
					DiagBuilder2::error(format!("Expected type definition after keyword `is`, found {} instead", tkn))
					.span(sp)
				);
				return Err(Reported);
			}
		}
	}

	if with_semicolon {
		require(p, Semicolon)?;
	}
	span.expand(p.last_span());
	Ok(())
}


/// Parse protected type declaration or body. See IEEE 1076-2008 section 5.6.
///
/// ```text
/// protected_type_decl := "protected" {decl_item} "end" "protected" [ident]
/// protected_type_body := "protected" "body" {decl_item} "end" "protected" "body" [ident]
/// ```
pub fn parse_protected_type_def<P: Parser>(p: &mut P, name: Spanned<Name>) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Protected))?;
	let body = accept(p, Keyword(Kw::Body));
	let decl_items = repeat(p, try_decl_item)?;
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::Protected))?;
	if body {
		require(p, Keyword(Kw::Body))?;
	}
	parse_optional_matching_ident(p, name, "type", "section 5.6");
	span.expand(p.last_span());
	Ok(())
}


/// Parse a subtype declaration. See IEEE 1076-2008 section 6.3.
///
/// ```text
/// subtype_decl := "subtype" ident "is" subtype_ind ";"
/// ```
pub fn parse_subtype_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Subtype))?;
	let name = parse_ident(p, "subtype name")?;
	require(p, Keyword(Kw::Is))?;
	let subtype = parse_subtype_ind(p)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


/// Parse an alias declaration. See IEEE 1076-2008 section 6.6.
///
/// ```text
/// alias_decl := "alias" alias_desig [":" subtype_ind] "is" name [signature] ";"
/// alias_desig := ident | char_lit | string_lit
/// ```
pub fn parse_alias_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
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
	let sig = try_flanked(p, Brack, parse_signature)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


pub fn parse_signature<P: Parser>(p: &mut P) -> ReportedResult<()> {
	unimp!(p, "Signatures");
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
pub fn parse_object_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;

	// Parse the object kind.
	let kind = match p.peek(0).value {
		Keyword(Kw::Constant) => { p.bump(); () },
		Keyword(Kw::Signal)   => { p.bump(); () },
		Keyword(Kw::File)     => { p.bump(); () },
		Keyword(Kw::Variable) => { p.bump(); () },
		Keyword(Kw::Shared)   => {
			p.bump();
			require(p, Keyword(Kw::Variable))?;
			()
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
		Keyword(Kw::Register) => { p.bump(); Some(()) },
		Keyword(Kw::Bus) => { p.bump(); Some(()) },
		Keyword(Kw::Open) | Keyword(Kw::Is) => {
			let open = if accept(p, Keyword(Kw::Open)) {
				Some(parse_expr(p)?)
			} else {
				None
			};
			require(p, Keyword(Kw::Is))?;
			let path = parse_expr(p)?;
			Some(())
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
	Ok(())
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
pub fn parse_subprog_spec<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;

	// Parse the optional purity qualifier.
	let purity = match p.peek(0).value {
		Keyword(Kw::Pure) => { p.bump(); Some(()) },
		Keyword(Kw::Impure) => { p.bump(); Some(()) },
		_ => None
	};

	// Parse the subprogram kind.
	let pk = p.peek(0);
	let kind = match pk.value {
		Keyword(Kw::Procedure) => { p.bump(); () },
		Keyword(Kw::Function) => { p.bump(); () },
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
				|p| parse_intf_decl(p, Some(IntfObjectKind::Constant))
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
				|p| parse_intf_decl(p, Some(IntfObjectKind::Variable))
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
	Ok(())
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
pub fn parse_component_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
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
	Ok(())
}


/// Parse a disconnection specification. See IEEE 1076-2008 section 7.4.
///
/// ```text
/// discon_spec := "disconnect" signal_list ":" name "after" expr ";"
/// signal_list := {name}","+ | "others" | "all"
/// ```
pub fn parse_discon_spec<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Disconnect))?;
	let signals = match p.peek(0).value {
		Keyword(Kw::Others) => { p.bump(); () },
		Keyword(Kw::All) => { p.bump(); () },
		_ => {
			separated_nonempty(p, Comma, Colon, "signal name", parse_name)?;
			()
		}
	};
	require(p, Colon)?;
	let ty = parse_name(p)?;
	require(p, Keyword(Kw::After))?;
	let after = parse_expr(p)?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
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
pub fn parse_block_comp_decl_item<P: Parser>(p: &mut P) -> ReportedResult<()> {
	match (p.peek(0).value, p.peek(1).value) {
		// vunit_binding_ind := "use" "vunit" ...
		(Keyword(Kw::Use), Keyword(Kw::Vunit)) => parse_vunit_binding_ind(p),
		// use_clause := "use" ...
		(Keyword(Kw::Use), _) => parse_use_clause(p),
		// block_comp_config := "for" ...
		(Keyword(Kw::For), _) => parse_block_comp_config(p),
		// attr_spec := "attribute" ...
		(Keyword(Kw::Attribute), _) => parse_attr_decl(p),
		// group_decl := "group" ...
		(Keyword(Kw::Group), _) => parse_group_decl(p),

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
pub fn parse_block_comp_config<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::For))?;
	let spec = parse_block_comp_spec(p)?;
	let bind = parse_binding_ind(p)?;
	let decl_items = repeat_until(p, Keyword(Kw::End), parse_block_comp_decl_item)?;
	require(p, Keyword(Kw::End))?;
	require(p, Keyword(Kw::For))?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
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
pub fn parse_binding_ind<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;

	/// Parse the entity aspect.
	let entity = if accept(p, Keyword(Kw::Use)) {
		let pk = p.peek(0);
		Some(match pk.value {
			Keyword(Kw::Entity) => {
				p.bump();
				parse_name(p)?;
				()
			}
			Keyword(Kw::Configuration) => {
				p.bump();
				parse_name(p)?;
				()
			}
			Keyword(Kw::Open) => {
				p.bump();
				()
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

	/// Parse the generic map aspect.
	let gm = try_map_aspect(p, Kw::Generic)?;

	/// Parse the port map aspect.
	let pm = try_map_aspect(p, Kw::Port)?;

	if entity.is_some() || gm.is_some() || pm.is_some() {
		require(p, Semicolon)?;
	}
	span.expand(p.last_span());
	Ok(())
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
pub fn parse_block_comp_spec<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;

	// Try to detect if this is a block or component specification.
	let spec = match (p.peek(0).value, p.peek(1).value) {
		(Keyword(Kw::Others), _) => {
			p.bump();
			require(p, Colon)?;
			let name = parse_name(p)?;
			()
		},

		(Keyword(Kw::All), _) => {
			p.bump();
			require(p, Colon)?;
			let name = parse_name(p)?;
			()
		}

		(Ident(_), Comma) | (Ident(_), Colon) => {
			let names = separated_nonempty(
				p,
				Comma,
				Colon,
				"label",
				|p| parse_ident(p, "label")
			);
			require(p, Colon)?;
			let name = parse_name(p)?;
			()
		}

		(wrong, _) => {
			if let Some(name) = try_name(p)? {
				()
			} else {
				let sp = p.peek(0).span;
				p.emit(
					DiagBuilder2::error(format!("Expected block name, component label, `all`, or `others`, foudn {} instead", wrong))
					.span(sp)
				);
				return Err(Reported);
			}
		}
	};

	span.expand(p.last_span());
	Ok(())
}


/// Parse a configuration specification. See IEEE 1076-2008 section 7.3.1.
///
/// ```text
/// config_spec := "for" block_comp_spec binding_ind {vunit_binding_ind} ["end" "for" ";"]
/// ```
pub fn parse_config_spec<P: Parser>(p: &mut P) -> ReportedResult<()> {
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
	Ok(())
}


/// Parse an attribute declaration or specification. See IEEE 1076-2008 sections
/// 6.7 and 7.2.
///
/// ```text
/// attribute_decl
///   := "attribute" ident ":" name ";"
///   := "attribute" ident "of" ({name [signature]}","+ | "others" | "all") ":" entity_class "is" expr ";"
/// ```
pub fn parse_attr_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Attribute))?;
	let name = parse_ident(p, "attribute name")?;

	// Depending on the next token, parse either a declaration or a
	// specification.
	if accept(p, Colon) {
		let ty = parse_name(p)?;
		require(p, Semicolon)?;
		span.expand(p.last_span());
		Ok(())
	} else if accept(p, Keyword(Kw::Of)) {
		// Parse the entity specification.
		let list = match p.peek(0).value {
			Keyword(Kw::Others) => { p.bump(); () }
			Keyword(Kw::All) => { p.bump(); () }
			_ => {
				let l = separated_nonempty(p, Comma, Colon, "name", |p|{
					let name = parse_name(p)?;
					let sig = try_flanked(p, Brack, parse_signature)?;
					Ok(())
				})?;
				()
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
		Ok(())
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
pub fn parse_entity_class<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let pk = p.peek(0);
	let cls = match pk.value {
		Keyword(Kw::Architecture) => (),
		Keyword(Kw::Component) => (),
		Keyword(Kw::Configuration) => (),
		Keyword(Kw::Constant) => (),
		Keyword(Kw::Entity) => (),
		Keyword(Kw::File) => (),
		Keyword(Kw::Function) => (),
		Keyword(Kw::Group) => (),
		Keyword(Kw::Label) => (),
		Keyword(Kw::Literal) => (),
		Keyword(Kw::Package) => (),
		Keyword(Kw::Procedure) => (),
		Keyword(Kw::Property) => (),
		Keyword(Kw::Sequence) => (),
		Keyword(Kw::Signal) => (),
		Keyword(Kw::Subtype) => (),
		Keyword(Kw::Type) => (),
		Keyword(Kw::Units) => (),
		Keyword(Kw::Variable) => (),
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
pub fn parse_group_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Group))?;
	let name = parse_ident(p, "group name")?;

	// Parse either a declaration or template declaration, depending on the next
	// token.
	if accept(p, Colon) {
		let ty = parse_name(p)?;
	} else if accept(p, Keyword(Kw::Is)) {
		let elems = flanked(p, Paren, |p| separated_nonempty(
			p, Comma, CloseDelim(Paren), "group element", |p|{
				let cls = parse_entity_class(p)?;
				let open = accept(p, LtGt);
				Ok(())
			}
		).map_err(|e| e.into()));
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
	}

	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


/// Parse a sequential statement.
pub fn parse_stmt<P: Parser>(p: &mut P) -> ReportedResult<()> {
	unimp!(p, "Statements");
}
