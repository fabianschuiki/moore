// Copyright (c) 2017 Fabian Schuiki

//! This module implements a first stage recursive descent parser for VHDL. It
//! can process a stream of input tokens into the coarse, generalized abstract
//! syntax tree defined in [`ast`]. The grammar productions/rules outlined in
//! the VHDL standard are collapsed into more general rules as outlined in the
//! following table.
//!
//! | VHDL Standard          | Generalized to       |
//! |------------------------|----------------------|
//! | name                   | name                 |
//! | name/simple_name       | primary_name         |
//! | name/operator_symbol   | primary_name         |
//! | name/character_literal | primary_name         |
//! | selected_name          | name                 |
//! | indexed_name           | name                 |
//! | slice_name             | name                 |
//! | attribute_name         | name                 |
//! | external_name          | *ignored*            |
//! | function_call          | name                 |
//! | type_mark              | name                 |
//! | subtype_indication     | name, primary_expr   |
//! | resolution_indication  | primary_expr         |
//! | constraint             | primary_expr         |
//! | range_constraint       | name                 |
//! | array_constraint       | name                 |
//! | record_constraint      | name, paren_expr     |

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
		Keyword(Kw::Configuration) => unimplemented!(),
		Keyword(Kw::Package) => {
			if p.peek(1).value == Keyword(Kw::Body) {
				parse_package_body(p)
			} else {
				parse_package_decl(p)
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
	if let Some(al) = try_flanked(p, Paren, parse_paren_expr)? {
		name.span.expand(p.last_span());
		name.parts.push(ast::NamePart::Call(ast::AssocList));
		return parse_name_suffix(p, name);
	}

	// Try to parse a range constraint.
	if accept(p, Keyword(Kw::Range)) {
		let expr = parse_expr_prec(p, ExprPrec::Range)?;
		name.span.expand(p.last_span());
		// name.part.push(ast::NamePart::Range);
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

	// Parse the generic part of the entity header. IEEE 1076-2008 section
	// 6.5.6.2.
	let generic = if accept(p, Keyword(Kw::Generic)) {
		let i = flanked(p, Paren, |p|{
			Ok(separated_nonempty(p,
				Semicolon,
				CloseDelim(Paren),
				"generic interface declaration",
				|p| parse_intf_decl(p, Some(IntfObjectKind::Constant))
			)?)
		})?;
		require(p, Semicolon)?;
		i
	} else {
		Vec::new()
	};

	// Parse the port part of the entity header. IEEE 1076-2008 section 6.5.6.3.
	let port = if accept(p, Keyword(Kw::Port)) {
		let i = flanked(p, Paren, |p|{
			Ok(separated_nonempty(p,
				Semicolon,
				CloseDelim(Paren),
				"port interface declaration",
				|p| parse_intf_decl(p, Some(IntfObjectKind::Signal))
			)?)
		})?;
		require(p, Semicolon)?;
		i
	} else {
		Vec::new()
	};

	// Parse the declarative part.
	repeat(p, parse_decl_item)?;

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


/// Parse an interface declaration. These are generally part of an interface
/// list as they appear in generic and port clauses within for example entity
/// declarations. See IEEE 1076-2008 section 6.5.1.
pub fn parse_intf_decl<P: Parser>(p: &mut P, default: Option<IntfObjectKind>) -> ReportedResult<()> {
	let Spanned{ value: tkn, mut span } = p.peek(0);

	// Try to parse one of the (non-file) object declarations.
	let kind = match tkn {
		Keyword(Kw::Constant) => { p.bump(); IntfObjectKind::Constant },
		Keyword(Kw::Signal) => { p.bump(); IntfObjectKind::Signal },
		Keyword(Kw::Variable) => { p.bump(); IntfObjectKind::Variable },
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
}


/// Parse a declarative item. See IEEE 1076-2008 section 3.2.3.
pub fn parse_decl_item<P: Parser>(p: &mut P) -> ReportedResult<Option<()>> {
	let Spanned{ value: tkn, span } = p.peek(0);
	Ok(match tkn {
		// package_decl := "package" ident "is" ...
		// package_body := "package" "body" ident "is" ...
		// package_inst := "package" ident "is" "new" ...
		Keyword(Kw::Package) => {
			if p.peek(1).value == Keyword(Kw::Body) {
				Some(parse_package_body(p)?)
			} else if p.peek(2).value == Keyword(Kw::Is) && p.peek(3).value == Keyword(Kw::New) {
				Some(parse_package_inst(p)?)
			} else {
				Some(parse_package_decl(p)?)
			}
		}
		_ => None
	})
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
			p.emit(
				DiagBuilder2::error("Association lists not yet supported")
				.span(q)
			);
			Err(Reported)
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
		Keyword(Kw::Null) => unimp!(p, "Null expressions"),
		Keyword(Kw::Open) => unimp!(p, "Open expressions"),
		Keyword(Kw::Others) => unimp!(p, "Others expressions"),

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


pub fn parse_package_decl<P: Parser>(p: &mut P) -> ReportedResult<()> {
	let mut span = p.peek(0).span;

	// Parse the head of the declaration.
	require(p, Keyword(Kw::Package))?;
	let name = parse_ident(p, "package name")?;
	require(p, Keyword(Kw::Is))?;

	// Parse the optional generic clause and generic map aspect.
	let gc = if accept(p, Keyword(Kw::Generic)) {
		let gc = flanked(p, Paren, parse_paren_expr)?;
		require(p, Semicolon)?;
		Some(gc)
	} else {
		None
	};

	let gm = if accept(p, Keyword(Kw::Generic)) {
		require(p, Keyword(Kw::Map))?;
		let gm = flanked(p, Paren, parse_paren_expr)?;
		require(p, Semicolon)?;
		Some(gm)
	} else {
		None
	};

	// Parse the declarative part.
	repeat(p, parse_decl_item)?;

	// Parse the tail of the declaration.
	require(p, Keyword(Kw::End))?;
	accept(p, Keyword(Kw::Package));
	parse_optional_matching_ident(p, name, "package", "section 4.7");
	require(p, Semicolon)?;
	span.expand(p.last_span());
	Ok(())
}


pub fn parse_package_body<P: Parser>(p: &mut P) -> ReportedResult<()> {
	unimp!(p, "Package bodies")
}


pub fn parse_package_inst<P: Parser>(p: &mut P) -> ReportedResult<()> {
	unimp!(p, "Package instance declarations")
}
