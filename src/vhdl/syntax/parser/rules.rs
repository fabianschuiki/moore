// Copyright (c) 2017 Fabian Schuiki

//! This module implements a recursive descent parser for VHDL.

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
		Keyword(Kw::Entity) => unimplemented!(),
		Keyword(Kw::Configuration) => unimplemented!(),
		Keyword(Kw::Package) => {
			if p.peek(1).value == Keyword(Kw::Body) {
				unimplemented!()
			} else {
				unimplemented!()
			}
		}
		Keyword(Kw::Context) => parse_context_decl(p),
		Keyword(Kw::Architecture) => unimplemented!(),
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
///   := name "(" assoc_list ")"
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
	if p.peek(0).value == OpenDelim(Brack) || p.peek(0).value == Apostrophe {
		// Parse the optional signature.
		let sig = try_flanked(p, Brack, |p| -> ReportedResult<()> {
			let q = p.peek(0).span;
			p.emit(
				DiagBuilder2::error("Signatures for attribute names not yet implemented")
				.span(q)
			);
			Err(Reported)
		})?;

		// Consume the apostrophe and attribute name.
		require(p, Apostrophe)?;
		let attr = parse_ident(p, "attribute name")?;

		// Extend the name.
		name.span.expand(p.last_span());
		name.parts.push(ast::NamePart::Attribute(attr, None));
		return parse_name_suffix(p, name);
	}

	// Try to parse a function call, slice name, or indexed name.
	if let Some(al) = try_flanked(p, Paren, parse_assoc_list)? {
		name.span.expand(p.last_span());
		name.parts.push(ast::NamePart::Call(ast::AssocList));
		return parse_name_suffix(p, name);
	}

	// If we arrive here, none of the suffices matched, and we simply return the
	// prefix that we have received.
	Ok(name)
}


/// Parse an association list as they are found in function calls. IEEE
/// 1076-2008 section 6.5.7.
///
/// ```text
/// assoc_list  := {assoc_elem}","+
/// assoc_elem  := [name "=>"] actual_part
/// actual_part
///   := expr
///   := "inertial" expr
///   := subtype_ind
///   := "open"
/// ```
pub fn parse_assoc_list<P: Parser>(p: &mut P) -> ReportedResult<()> {
	unimp!(p, "Association lists");
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
	match try_ident(p) {
		Some(n) if n.value != name.value => {
			p.emit(
				DiagBuilder2::warning(format!("`{}` does not match the context's name `{}`", n.value, name.value))
				.span(n.span)
				.add_note("see IEEE 1076-2008 section 13.3")
			);
		}
		_ => ()
	}
	require(p, Semicolon);
	Ok(())
}
