// Copyright (c) 2017 Fabian Schuiki

//! This file implements a recursive descent parser for VHDL.

use moore_common::errors::*;
use moore_common::name::*;
use moore_common::source::*;
use syntax::lexer::token::*;
use syntax::parser::TokenStream;
use syntax::parser::core::*;

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


pub fn parse_design_file<P: Parser>(p: &mut P) {
	let mut units = Vec::new();
	while !p.is_fatal() && p.peek(0).value != Eof {
		match parse_design_unit(p) {
			Ok(unit) => units.push(unit),
			Err(Recovered) => ()
		}
	}
}


pub fn parse_design_unit<P: Parser>(p: &mut P) -> RecoveredResult<()> {
	let context = repeat(p, parse_context_item)?;
	let Spanned{ value: tkn, span: sp } = p.peek(0);
	match tkn {
		Keyword(Kw::Entity) => unimplemented!(),
		Keyword(Kw::Configuration) => unimplemented!(),
		Keyword(Kw::Package) => unimplemented!(),
		Keyword(Kw::Context) => unimplemented!(),
		Keyword(Kw::Architecture) => unimplemented!(),
		tkn => {
			p.emit(
				DiagBuilder2::error(format!("Expected a primary or secondary unit, instead found {}", tkn))
				.span(sp)
				.add_note("`entity`, `configuration`, `package`, and `context` are primary units")
				.add_note("`architecture` and `package body` are secondary units")
			);
			recover(p, &[Keyword(Kw::End)], true);
			recover(p, &[Semicolon], true);
			return Err(Recovered);
		}
	}
}


/// Parse a context item.
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


/// Parse a library clause.
///
/// ```text
/// library_clause := "library" ident {"," ident}
/// ```
pub fn parse_library_clause<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;
	require(p, Keyword(Kw::Library))?;
	let names = separated_nonempty(p, Comma, Semicolon, "library name", |p| parse_ident(p, "library name"))?;
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


/// Parse a use clause.
///
/// ```text
/// use_clause := "use" {name ","}+
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
	unimp!(p, "Context references");
}


/// Parse a name.
pub fn parse_name<P: Parser>(p: &mut P) -> ReportedResult<()> {
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


/// Try to parse a name.
///
/// ```text
/// primary_name := ident | char_lit | string_lit
/// ```
pub fn try_name<P: Parser>(p: &mut P) -> ReportedResult<Option<()>> {
	let Spanned{ value: tkn, mut span } = p.peek(0);

	// Parse a primary name.
	let primary = match tkn {
		Ident(n) => { p.bump(); () },
		Lit(Literal::Char(c)) => { p.bump(); () },
		Lit(Literal::String(s)) => { p.bump(); () },
		_ => return Ok(None)
	};

	// Parse a potential name suffix.
	parse_name_suffix(p, primary).map(|x| Some(x))
}


/// Parse the suffix to a name.
///
/// ```text
/// name
///   := primary_name
///   := name "." (ident | char_lit | string_lit | "all")
///   := name [signature] "'" ident
///   := name "(" assoc_list ")"
/// ```
pub fn parse_name_suffix<P: Parser>(p: &mut P, prefix: ()) -> ReportedResult<()> {
	// Try to parse a selected name.
	if accept(p, Period) {
		let Spanned{ value: tkn, mut span } = p.peek(0);
		let name = match tkn {
			Ident(n) => { p.bump(); () },
			Lit(Literal::Char(c)) => { p.bump(); () },
			Lit(Literal::String(s)) => { p.bump(); () },
			Keyword(Kw::All) => { p.bump(); () }
			wrong => {
				p.emit(
					DiagBuilder2::error("Expected identifier, character literal, or operator symbol after `.`")
					.span(span)
					.add_note("see IEEE 1076-2008 section 8.3")
				);
				return Err(Reported);
			}
		};
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
		let name = parse_ident(p, "attribute name")?;
		return parse_name_suffix(p, ());
	}

	// Try to parse a function call, slice name, or indexed name.
	if let Some(al) = try_flanked(p, Paren, parse_assoc_list)? {
		return parse_name_suffix(p, ());
	}

	// If we arrive here, none of the suffices matched, and we simply return the
	// prefix that we have received.
	Ok(prefix)
}


/// Parse an association list as they are found in function calls.
///
/// ```text
/// assoc_list  := {assoc_elem ","}+
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
