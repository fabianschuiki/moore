// Copyright (c) 2016 Fabian Schuiki

//! A parser for VHDL token streams, based on IEEE 1076-2000.

use errors::{DiagnosticBuilder, DiagResult, DUMMY_HANDLER};
use vhdl::lexer::{Lexer, Span};
use vhdl::name::Name;
use vhdl::token::{self, Token, keywords};
use vhdl::ast::*;


pub struct Parser {
	pub lexer: Box<Lexer>,
	pub token: Token,
	pub span: Span,
}

impl<'a> Parser {
	pub fn new(mut lexer: Box<Lexer>) -> Parser {
		let next = match lexer.next_token() {
			Ok(tknspn) => tknspn,
			Err(_) => panic!("initial token invalid"),
		};

		Parser {
			lexer: lexer,
			token: next.tkn,
			span: next.sp,
		}
	}

	/// Advance the parser by one token.
	fn next(&mut self) -> DiagResult<'a,()> {
		let next = try!(self.lexer.next_token());
		self.token = next.tkn;
		self.span = next.sp;
		Ok(())
	}

	fn eat(&mut self, token: &token::Token) -> DiagResult<'a, bool> {
		if self.token == *token {
			try!(self.next());
			Ok(true)
		} else {
			Ok(false)
		}
	}

	/// If the current token is the given keyword, consume it and return true.
	/// Otherwise return false.
	fn eat_keyword(&mut self, kw: Name) -> DiagResult<'a, bool> {
		if self.check_keyword(kw) {
			try!(self.next());
			Ok(true)
		} else {
			Ok(false)
		}
	}

	/// Check if the current token is the given keyword.
	fn check_keyword(&mut self, kw: Name) -> bool {
		self.token.is_keyword(kw)
	}

	fn expect(&mut self, tkn: &token::Token) -> DiagResult<'a,()> {
		if self.token == *tkn {
			try!(self.next());
			Ok(())
		} else {
			let exp_token_str = Self::token_to_string(tkn);
			let act_token_str = self.this_token_to_string();
			Err(self.fatal(&format!(
				"expected `{}`, found `{}`",
				exp_token_str,
				act_token_str
			)))
		}
	}

	fn this_token_to_string(&self) -> String {
		Self::token_to_string(&self.token)
	}

	fn token_to_string(tkn: &token::Token) -> String {
		tkn.to_string()
	}

	fn fatal(&self, msg: &str) -> DiagnosticBuilder<'a> {
		DiagnosticBuilder {
			handler: &DUMMY_HANDLER,
			message: String::from(msg),
		}
	}

	/// This is the main entry point into the parser.
	pub fn parse_design_file(&mut self) -> DiagResult<'a, Vec<Box<DesignUnit>>> {
		let mut units: Vec<Box<DesignUnit>> = Vec::new();
		while let Some(unit) = try!(self.parse_design_unit()) {
			units.push(unit);
		}
		if !try!(self.eat(&token::Eof)) {
			let token_str = self.this_token_to_string();
			return Err(self.fatal(&format!("expected design unit, found `{}`", token_str)));
		}
		Ok(units)
	}

	/// Parse a design unit. See IEEE 1076-2000 section 11.1.
	fn parse_design_unit(&mut self) -> DiagResult<'a, Option<Box<DesignUnit>>> {
		// Parse the context clauses.
		let mut ctx_clauses = Vec::new();
		while let Some(cc) = try!(self.parse_context_clause()) {
			println!("parsed a context clause");
			ctx_clauses.push(cc);
		}

		// Parse the library unit.
		Err(self.fatal("not implemented"))
	}

	/// Parse a context clause. See IEEE 1076-2000 section 11.3.
	fn parse_context_clause(&mut self) -> DiagResult<'a, Option<Box<ContextClause>>> {
		// Library clause
		// LIBRARY logical_name {COMMA logical_name} SEMICOLON
		if try!(self.eat_keyword(keywords::Library)) {
			let mut names = Vec::new();
			while let Some(ln) = try!(self.parse_logical_name()) {
				names.push(ln);
				if !try!(self.eat(&token::Comma)) {
					break;
				}
			}
			try!(self.expect(&token::Semicolon));
			return Ok(Some(Box::new(ContextClause::Library(names))));
		}

		// Use clause
		// USE selected_name {COMMA selected_name} SEMICOLON
		if try!(self.eat_keyword(keywords::Use)) {
			let mut names = Vec::new();
			while let Some(sn) = try!(self.parse_selected_name()) {
				names.push(sn);
				if !try!(self.eat(&token::Comma)) {
					break;
				}
			}
			try!(self.expect(&token::Semicolon));
			return Ok(Some(Box::new(ContextClause::Use(names))));
		}

		Ok(None)
	}

	fn parse_logical_name(&mut self) -> DiagResult<'a, Option<Name>> {
		match self.token {
			token::Ident(nm) => {
				try!(self.next());
				Ok(Some(nm))
			},
			_ => Ok(None)
		}
	}

	/// Parse a name. See IEEE 1076-2000 section 6.
	/// IDENT|OP PERIOD IDENT|CHARLIT|OP|ALL ...
	/// IDENT|OP LPAREN expr (, expr)* RPAREN ...
	/// IDENT|OP LPAREN discrete_range RPAREN ...
	/// IDENT|OP (LBRACK signature RBRACK)? APOSTROPHE IDENT (LPAREN expr RPAREN)? ...
	fn parse_name(&mut self) -> DiagResult<'a, Option<u32>> {

	}

	/// Parse a selected name. See IEEE 1076-2000 section 6.3.
	fn parse_selected_name(&mut self) -> DiagResult<'a, Option<Name>> {
		// Parse the prefix.
		// simple_name=IDENT | operator_symbol=OP | selected_name | indexed_name | slice_name | attribute_name | function_call

		// Parse the suffix.
		// simple_name | character_literal | operator_symbol | ALL

		Ok(None)
	}
}
