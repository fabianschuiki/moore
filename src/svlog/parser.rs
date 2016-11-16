// Copyright (c) 2016 Fabian Schuiki

//! A parser for the SystemVerilog language. Based on IEEE 1800-2009.

use svlog::lexer::{Lexer, TokenAndSpan};
use svlog::token::*;
use std::collections::VecDeque;
use errors::*;
use svlog::ast::*;
use name::*;
use source::*;


/// Return type of the lower parse primitives, allowing for further adjustment
/// of the diagnostic message that would be generated.
type ParseResult<T> = Result<T, DiagBuilder2>;

/// Return type of functions that emit diagnostic messages and only need to
/// communicate success to the parent.
type ReportedResult<T> = Result<T, ()>;


struct Parser<'a> {
	input: Lexer<'a>,
	queue: VecDeque<TokenAndSpan>,
	diagnostics: Vec<DiagBuilder2>,
}

impl<'a> Parser<'a> {
	fn new(input: Lexer) -> Parser {
		Parser {
			input: input,
			queue: VecDeque::new(),
			diagnostics: Vec::new(),
		}
	}

	fn ensure_queue_filled(&mut self, min_tokens: usize) {
		if let Some(&(Eof,_)) = self.queue.back() {
			return;
		}
		while self.queue.len() <= min_tokens {
			match self.input.next_token() {
				Ok((Eof, sp)) => self.queue.push_back((Eof, sp)),
				Ok(tkn) => self.queue.push_back(tkn),
				Err(x) => self.add_diag(x),
			}
		}
	}

	fn peek(&mut self, offset: usize) -> TokenAndSpan {
		self.ensure_queue_filled(offset);
		if offset < self.queue.len() {
			self.queue[offset]
		} else {
			*self.queue.back().expect("At least an Eof token should be in the queue")
		}
	}

	fn bump(&mut self) {
		if self.queue.is_empty() {
			self.ensure_queue_filled(1);
		}
		self.queue.pop_front();
	}

	fn add_diag(&mut self, diag: DiagBuilder2) {
		println!("*** {:?}", diag);
		self.diagnostics.push(diag);
		// TODO: Keep track of the worst diagnostic encountered, such that fatal
		// errors can properly abort parsing.
	}

	fn get_diagnostics(&self) -> &[DiagBuilder2] {
		&self.diagnostics
	}

	fn is_fatal(&self) -> bool {
		false
	}

	fn eat_ident_or(&mut self, msg: &str) -> ParseResult<(Name, Span)> {
		match self.peek(0) {
			(Ident(name), span) => { self.bump(); Ok((name, span)) },
			(tkn, span) => Err(DiagBuilder2::error(format!("Expected {} before {:?}", msg, tkn)).span(span)),
		}
	}

	fn require(&mut self, expect: Token) -> Result<(), DiagBuilder2> {
		match self.peek(0) {
			(actual, _) if actual == expect => { self.bump(); Ok(()) },
			(wrong, span) => Err(DiagBuilder2::error(format!("Expected {:?}, but found {:?} instead", expect, wrong)).span(span))
		}
	}

	fn try_eat(&mut self, expect: Token) -> bool {
		match self.peek(0) {
			(actual, span) if actual == expect => { self.bump(); true},
			_ => false
		}
	}

	fn recover_balanced(&mut self, terminators: &[Token]) {
		let mut stack = Vec::new();
		loop {
			let (tkn, sp) = self.peek(0);
			if stack.is_empty() {
				for t in terminators {
					if *t == tkn {
						return;
					}
				}
			}

			match tkn {
				OpenDelim(x) => stack.push(x),
				CloseDelim(x) => {
					if let Some(open) = stack.pop() {
						if open == x {
							break;
						} else {
							self.add_diag(DiagBuilder2::error(format!("Found closing {:?} which is not the complement to the previous opening {:?}", x, open)).span(sp));
							break;
						}
					} else {
						self.add_diag(DiagBuilder2::error(format!("Found closing {:?} without an earlier opening {:?}", x, x)).span(sp));
						break;
					}
				}
				_ => (),
			}
			self.bump();
		}
	}
}


pub fn parse(input: Lexer) {
	let mut p = Parser::new(input);
	parse_source_text(&mut p);
	assert!(p.get_diagnostics().is_empty());
}

fn parse_source_text(p: &mut Parser) {
	// Parse the optional timeunits declaration.
	// TODO

	// Parse the descriptions in the source text.
	loop {
		let good = match p.peek(0) {
			(Keyword(Kw::Module), _) => {
				p.bump();
				match parse_module_decl(p) {
					Some(_) => true,
					None => false,
				}
			}
			(Keyword(Kw::Interface),_) => {
				p.bump();
				match parse_interface_decl(p) {
					Some(_) => true,
					None => false,
				}
			}
			(Eof,_) => break,
			(tkn,sp) => {
				p.add_diag(DiagBuilder2::fatal(format!("Expected top-level description, instead got `{:?}`", tkn)).span(sp));
				false
			}
		};

		// Recover by scanning forward to the next endmodule or endinterface.
		if !good {
			loop {
				match p.peek(0) {
					(Keyword(Kw::Endmodule), _) |
					(Keyword(Kw::Endinterface), _) => { p.bump(); break; },
					(Eof, _) => break,
					_ => p.bump(),
				}
			}
		}
	}
}


fn parse_interface_decl(p: &mut Parser) -> Option<IntfDecl> {
	println!("interface");

	// TODO: Parse optional lifetime.

	// Eat the interface name.
	let (name, name_sp) = match p.eat_ident_or("interface name") {
		Ok(x) => x,
		Err(x) => { p.add_diag(x); return None; }
	};
	println!("interface {}", name);

	// TODO: Parse package import declarations.

	// Eat the parameter port list.
	if p.try_eat(Hashtag) {
		parse_parameter_port_list(p);
	}

	// Eat either the list of ports or port declarations, depending on whether
	// this is an ANSI or non-ANSI interface header.

	// Eat the semicolon at the end of the header.
	if !p.try_eat(Semicolon) {
		let q = p.peek(0).1.end();
		p.add_diag(DiagBuilder2::error(format!("Missing semicolon \";\" after header of interface \"{}\"", name)).span(q));
	}

	// Eat the endinterface keyword.
	if !p.try_eat(Keyword(Kw::Endinterface)) {
		let q = p.peek(0).1.end();
		p.add_diag(DiagBuilder2::error(format!("Missing \"endinterface\" at the end of \"{}\"", name)).span(q));
	}

	Some(IntfDecl {
		name: name,
		name_span: name_sp,
		span: name_sp,
	})
	// None
	// loop {
	// 	match p.peek(0) {
	// 		(Keyword(Kw::Endinterface), _) => { p.bump(); break; },
	// 		(Eof, _) => break,
	// 		_ => p.bump(),
	// 	}
	// }
	// Ok(())
}


fn parse_parameter_port_list(p: &mut Parser) {
	match p.require(OpenDelim(Paren)) {
		Ok(()) => (),
		Err(e) => { p.add_diag(e); return; }
	}

	while p.try_eat(Keyword(Kw::Parameter)) {
		// TODO: Parse data type or implicit type.

		// Eat the list of parameter assignments.
		// parameter_identifier { unpacked_dimension } [ = constant_param_expression ]
		let (name, name_sp) = match p.eat_ident_or("parameter name") {
			Ok(x) => x,
			Err(e) => {
				p.add_diag(e);
				p.recover_balanced(&[Comma, CloseDelim(Paren)]);
				break;
			}
		};

		// TODO: Eat the unpacked dimensions.

		if p.try_eat(Assign) {
			let q = p.peek(0).1.end();
			p.add_diag(DiagBuilder2::error("Parameter assignment not implemented").span(q));
			p.recover_balanced(&[Comma, CloseDelim(Paren)]);
		}
	}

	match p.require(CloseDelim(Paren)) {
		Ok(()) => (),
		Err(e) => p.add_diag(e)
	}
}


fn parse_module_decl(p: &mut Parser) -> Option<ModDecl> {
	println!("module");
	p.add_diag(DiagBuilder2::fatal("Modules not implemented"));
	None
	// loop {
	// 	match p.peek(0) {
	// 		(Keyword(Kw::Endmodule), _) => { p.bump(); break; },
	// 		(Eof, _) => break,
	// 		_ => p.bump(),
	// 	}
	// }
	// Ok(())
}


#[cfg(test)]
mod tests {
	use source::*;
	use name::*;
	use svlog::preproc::*;
	use svlog::lexer::*;

	fn parse(input: &str) {
		use std::cell::Cell;
		thread_local!(static INDEX: Cell<usize> = Cell::new(0));
		let sm = get_source_manager();
		let idx = INDEX.with(|i| {
			let v = i.get();
			i.set(v+1);
			v
		});
		let source = sm.add(&format!("test_{}.sv", idx), input);
		let pp = Preprocessor::new(source, &[]);
		let lexer = Lexer::new(pp);
		super::parse(lexer);
	}

	#[test]
	fn intf_empty() {
		parse("interface Foo; endinterface");
	}

	#[test]
	fn intf_params() {
		parse("interface Foo #(); endinterface");
		parse("interface Foo #(parameter bar = 32); endinterface");
		parse("interface Foo #(parameter bar = 32, baz = 64); endinterface");
		parse("interface Foo #(parameter bar = 32, parameter baz = 64); endinterface");
	}

	#[test]
	fn intf_header() {
		// parse("interface Foo ();")
	}
}
