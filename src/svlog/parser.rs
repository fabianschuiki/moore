// Copyright (c) 2016 Fabian Schuiki

//! A parser for the SystemVerilog language. Based on IEEE 1800-2009.

use svlog::lexer::{Lexer, TokenAndSpan};
use svlog::token::*;
use std::collections::VecDeque;
use errors::*;
use svlog::ast::*;
use name::*;
use source::*;

// The problem with data_declaration and data_type_or_implicit:
//
//     [7:0] foo;            # implicit "[7:0]", var "foo"
//     foo bar;              # explicit "foo", var "bar"
//     foo [7:0];            # implicit, var "foo[7:0]"
//     foo [7:0] bar [7:0];  # explicit "foo[7:0]", var "bar[7:0]"


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
			(EscIdent(name), span) => { self.bump(); Ok((name, span)) },
			(tkn, span) => Err(DiagBuilder2::error(format!("Expected {} before {:?}", msg, tkn)).span(span)),
		}
	}

	fn eat_ident(&mut self, msg: &str) -> ReportedResult<(Name, Span)> {
		match self.peek(0) {
			(Ident(name), span) => { self.bump(); Ok((name, span)) }
			(EscIdent(name), span) => { self.bump(); Ok((name, span)) }
			(tkn, span) => {
				self.add_diag(DiagBuilder2::error(format!("Expected {} before {:?}", msg, tkn)).span(span));
				Err(())
			}
		}
	}

	fn require(&mut self, expect: Token) -> Result<(), DiagBuilder2> {
		match self.peek(0) {
			(actual, _) if actual == expect => { self.bump(); Ok(()) },
			(wrong, span) => Err(DiagBuilder2::error(format!("Expected {:?}, but found {:?} instead", expect, wrong)).span(span))
		}
	}

	fn require_reported(&mut self, expect: Token) -> ReportedResult<()> {
		match self.require(expect) {
			Ok(x) => Ok(x),
			Err(e) => {
				self.add_diag(e);
				Err(())
			}
		}
	}

	fn try_eat(&mut self, expect: Token) -> bool {
		match self.peek(0) {
			(actual, span) if actual == expect => { self.bump(); true},
			_ => false
		}
	}

	fn recover(&mut self, terminators: &[Token], eat_terminator: bool) {
		println!("recovering to {:?}", terminators);
		loop {
			match self.peek(0) {
				(Eof, _) => return,
				(tkn, _) => {
					for t in terminators {
						if *t == tkn {
							if eat_terminator {
								self.bump();
							}
							return;
						}
					}
					self.bump();
				}
			}
		}
	}

	fn recover_balanced(&mut self, terminators: &[Token]) {
		println!("recovering (balanced) to {:?}", terminators);
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
				Eof => break,
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
					Ok(_) => true,
					Err(_) => false,
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


pub enum Lifetime {
	Static,
	Automatic,
}

fn as_lifetime(tkn: Token) -> Option<Lifetime> {
	match tkn {
		Keyword(Kw::Static) => Some(Lifetime::Static),
		Keyword(Kw::Automatic) => Some(Lifetime::Automatic),
		_ => None,
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

	// Eat the items in the interface.
	while p.peek(0).0 != Keyword(Kw::Endinterface) {
		match try_hierarchy_item(p) {
			Some(Ok(())) => (),
			Some(Err(())) => (),
			None => {
				let (tkn, q) = p.peek(0);
				p.add_diag(DiagBuilder2::error(format!("Expected hierarchy item, got {:?}", tkn)).span(q));
				p.recover(&[Keyword(Kw::Endinterface)], false);
			}
		}
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
		loop {
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
				match parse_constant_expr(p) {
					Ok(_) => (),
					Err(_) => p.recover_balanced(&[Comma, CloseDelim(Paren)])
				}
				// let q = p.peek(0).1.end();
				// p.add_diag(DiagBuilder2::error("Parameter assignment not implemented").span(q));
			}

			// Eat the trailing comma or closing parenthesis.
			match p.peek(0) {
				(Comma, sp) => {
					p.bump();
					match p.peek(0) {
						// The `parameter` keyword terminates this list of
						// assignments and introduces the next parameter.
						(Keyword(Kw::Parameter), _) => break,

						// A closing parenthesis indicates that the previous
						// comma was superfluous. Report the issue but continue
						// gracefully.
						(CloseDelim(Paren), _) => {
							// TODO: This should be an error in pedantic mode.
							p.add_diag(DiagBuilder2::warning("Superfluous trailing comma").span(sp));
							break;
						}

						// All other tokens indicate the next assignment in the
						// list, so we just continue with the next iteration.
						_ => continue,
					}
				},
				(CloseDelim(Paren), _) => break,
				(_, sp) => {
					p.add_diag(DiagBuilder2::error("Expected , or ) after parameter assignment").span(sp));
					p.recover_balanced(&[CloseDelim(Paren)]);
					break;
				}
			}
		}
	}

	match p.require(CloseDelim(Paren)) {
		Ok(()) => (),
		Err(e) => p.add_diag(e)
	}
}


fn parse_constant_expr(p: &mut Parser) -> ReportedResult<()> {
	let (tkn, span) = p.peek(0);

	// Try the unary operators.
	let unary_op = match tkn {
		Add =>  Some(()),
		Sub =>  Some(()),
		Not =>  Some(()),
		Neg =>  Some(()),
		And =>  Some(()),
		Nand => Some(()),
		Or =>   Some(()),
		Xor =>  Some(()),
		Nxor => Some(()),
		Xnor => Some(()),
		_ => None,
	};
	if let Some(x) = unary_op {
		p.bump();
		return parse_constant_expr(p);
	}

	// Parse the constant primary.
	let expr = match tkn {
		// Primary literals.
		UnsignedNumber(x) => { p.bump(); () },
		Literal(Str(x)) => { p.bump(); () },
		Literal(BasedInteger(size, signed, base, value)) => { p.bump(); () },
		Literal(UnbasedUnsized(x)) => { p.bump(); () },
		Ident(x) => { p.bump(); () },
		_ => {
			p.add_diag(DiagBuilder2::error("Expected constant primary expression").span(span));
			return Err(());
		}
	};

	// Try the binary operators.
	let (tkn, span) = p.peek(0);
	let binary_op = match tkn {
		Add =>  Some(()),
		Sub =>  Some(()),
		Mul =>  Some(()),
		Div =>  Some(()),
		Mod =>  Some(()),
		And =>  Some(()),
		Or =>  Some(()),
		Xor =>  Some(()),
		Xnor =>  Some(()),
		Nxor =>  Some(()),
		_ => None,
	};
	if let Some(x) = binary_op {
		p.bump();
		return parse_constant_expr(p);
	}

	// TODO: Parse ternary operator.

	Ok(())
}


/// Parse a module declaration, assuming that the leading `module` keyword has
/// already been consumed.
fn parse_module_decl(p: &mut Parser) -> ReportedResult<ModDecl> {

	// Eat the optional lifetime.
	let lifetime = as_lifetime(p.peek(0).0);
	if lifetime.is_some() {
		p.bump();
	}

	// Eat the module name.
	let (name, name_sp) = p.eat_ident("module name")?;
	println!("module {}", name);

	// TODO: Parse package import declarations.

	// Eat the optional parameter port list.
	if p.try_eat(Hashtag) {
		parse_parameter_port_list(p);
	}

	// Eat the optional list of ports. Not having such a list requires the ports
	// to be defined further down in the body of the module.
	if p.try_eat(OpenDelim(Paren)) {
		let q = p.peek(0).1;
		p.add_diag(DiagBuilder2::fatal("Module ports not implemented").span(q));
		p.recover(&[CloseDelim(Paren)], true);
	}

	// Eat the semicolon after the header.
	if !p.try_eat(Semicolon) {
		let q = p.peek(0).1.end();
		p.add_diag(DiagBuilder2::error(format!("Missing ; after header of module \"{}\"", name)).span(q));
	}

	// Eat the items in the interface.
	while p.peek(0).0 != Keyword(Kw::Endmodule) {
		match try_hierarchy_item(p) {
			Some(Ok(())) => (),
			Some(Err(())) => (),
			None => {
				let (tkn, q) = p.peek(0);
				p.add_diag(DiagBuilder2::error(format!("Expected hierarchy item, got {:?}", tkn)).span(q));
				p.recover(&[Keyword(Kw::Endmodule)], false);
			}
		}
	}

	// Eat the endmodule keyword.
	if !p.try_eat(Keyword(Kw::Endmodule)) {
		let q = p.peek(0).1.end();
		p.add_diag(DiagBuilder2::error(format!("Missing \"endmodule\" at the end of \"{}\"", name)).span(q));
	}

	Ok(ModDecl {
		name: name,
		name_span: name_sp,
		span: name_sp,
	})
}


fn try_hierarchy_item(p: &mut Parser) -> Option<ReportedResult<()>> {
	// First attempt the simple cases where a keyword reliably identifies the
	// following item.
	let (tkn, _) = p.peek(0);
	let f = |p, func, term| Some(hierarchy_item_wrapper(p, func, term));
	match tkn {
		Keyword(Kw::Localparam) => return f(p, parse_localparam_decl, Semicolon),
		Keyword(Kw::Parameter) => return f(p, parse_parameter_decl, Semicolon),
		Keyword(Kw::Modport) => return f(p, parse_modport_decl, Semicolon),
		_ => ()
	}

	// TODO: Handle the const and var keywords that may appear in front of a
	// data declaration, as well as the optional lifetime.

	// Now attempt to parse a data type or implicit type, which could introduce
	// and instantiation or data declaration. Due to the nature of implicit
	// types, a data declaration such as `foo[7:0];` would initially parse as an
	// explicit type `foo[7:0]`, and can only be identified as having an
	// implicit type when the semicolon is parsed. I.e. declarations that appear
	// to consist only of a type are actually declarations with an implicit
	// type.
	let ty = match parse_data_type(p) {
		Ok(x) => x,
		Err(_) => {
			p.recover(&[Semicolon], true);
			return Some(Err(()));
		}
	};

	// TODO: Handle the special case where the token following the parsed data
	// type is a [,;=], which indicates that the parsed type is actually a
	// variable declaration with implicit type (they look the same).

	// Parse the list of variable declaration assignments.
	loop {
		let (name, span) = match p.eat_ident_or("variable name") {
			Ok(x) => x,
			Err(e) => {
				p.add_diag(e);
				return Some(Err(()));
			}
		};

		// Parse the optional variable dimensions.
		let dims = match parse_optional_dimensions(p) {
			Ok(x) => x,
			Err(_) => return Some(Err(())),
		};

		// Parse the optional assignment.
		if p.try_eat(Assign) {
			let q = p.peek(0).1;
			p.add_diag(DiagBuilder2::error("Default variable assignments not implemented").span(q));
			p.recover(&[Comma, Semicolon], false);
		}

		// Either parse the next variable declaration or break out of the loop
		// if we have encountered the semicolon that terminates the statement.
		match p.peek(0) {
			(Semicolon, _) => { p.bump(); break; },
			(Comma, sp) => {
				p.bump();
				if p.peek(0).0 == Semicolon {
					// TODO: Make this an error in pedantic mode.
					p.add_diag(DiagBuilder2::warning("Superfluous trailing comma").span(sp));
					p.bump();
					break;
				} else {
					continue;
				}
			}
			(_, sp) => {
				p.add_diag(DiagBuilder2::error("Expected , or ; after variable declaration").span(sp));
				p.recover(&[Semicolon], true);
				return Some(Err(()));
			}
		}
	}

	Some(Ok(()))
}


fn hierarchy_item_wrapper(p: &mut Parser, func: fn(&mut Parser) -> ReportedResult<()>, term: Token) -> ReportedResult<()> {
	p.bump();
	match func(p) {
		Ok(x) => {
			match p.require(Semicolon) {
				Err(d) => p.add_diag(d),
				_ => ()
			}
			Ok(x)
		}
		Err(e) => {
			p.recover(&[term], true);
			Err(e)
		}
	}
}


fn parse_localparam_decl(p: &mut Parser) -> ReportedResult<()> {
	// TODO: Parse data type or implicit type.

	// Eat the list of parameter assignments.
	loop {
		// parameter_identifier { unpacked_dimension } [ = constant_param_expression ]
		let (name, name_sp) = match p.eat_ident_or("parameter name") {
			Ok(x) => x,
			Err(e) => {
				p.add_diag(e);
				return Err(());
			}
		};

		// TODO: Eat the unpacked dimensions.

		// Eat the optional assignment.
		if p.try_eat(Assign) {
			match parse_constant_expr(p) {
				Ok(_) => (),
				Err(_) => p.recover_balanced(&[Comma, CloseDelim(Paren)])
			}
		}

		// Eat the trailing comma or semicolon.
		match p.peek(0) {
			(Comma, sp) => {
				p.bump();

				// A closing parenthesis indicates that the previous
				// comma was superfluous. Report the issue but continue
				// gracefully.
				if p.peek(0).0 == Semicolon {
					// TODO: This should be an error in pedantic mode.
					p.add_diag(DiagBuilder2::warning("Superfluous trailing comma").span(sp));
					break;
				}
			},
			(Semicolon, _) => break,
			(x, sp) => {
				p.add_diag(DiagBuilder2::error(format!("Expected , or ; after parameter assignment, got `{:?}`", x)).span(sp));
				return Err(());
			}
		}
	}

	Ok(())
}


fn parse_parameter_decl(p: &mut Parser) -> ReportedResult<()> {
	let q = p.peek(0).1;
	p.add_diag(DiagBuilder2::error("Parameter declarations not implemented").span(q));
	Err(())
}


/// Parse a modport declaration.
///
/// ```
/// modport_decl: "modport" modport_item {"," modport_item} ";"
/// modport_item: ident "(" modport_ports_decl {"," modport_ports_decl} ")"
/// modport_ports_decl:
///   port_direction modport_simple_port {"," modport_simple_port} |
///   ("import"|"export") modport_tf_port {"," modport_tf_port} |
///   "clocking" ident
/// modport_simple_port: ident | "." ident "(" [expr] ")"
/// ```
fn parse_modport_decl(p: &mut Parser) -> ReportedResult<()> {
	loop {
		parse_modport_item(p)?;
		match p.peek(0) {
			(Comma, sp) => {
				p.bump();
				if let (Semicolon, _) = p.peek(0) {
					p.add_diag(DiagBuilder2::warning("Superfluous trailing comma").span(sp));
					break;
				} else {
					continue;
				}
			},
			(Semicolon, _) => break,
			(x, sp) => {
				p.add_diag(DiagBuilder2::error(format!("Expected , or ; after modport declaration, got `{:?}`", x)).span(sp));
				return Err(());
			}
		}
	}

	Ok(())
}


fn parse_modport_item(p: &mut Parser) -> ReportedResult<()> {
	let (name, span) = match p.eat_ident_or("modport name") {
		Ok(x) => x,
		Err(e) => {
			p.add_diag(e);
			return Err(());
		}
	};
	println!("modport {}", name);

	// Eat the opening parenthesis.
	if !p.try_eat(OpenDelim(Paren)) {
		let (tkn, q) = p.peek(0);
		p.add_diag(DiagBuilder2::error(format!("Expected ( after modport name `{}`, got `{:?}`", name, tkn)).span(q));
		return Err(());
	}

	// Parse the port declarations.
	loop {
		match parse_modport_port_decl(p) {
			Ok(x) => x,
			Err(_) => {
				p.recover(&[CloseDelim(Paren)], true);
				return Err(());
			}
		}
		match p.peek(0) {
			(Comma, sp) => {
				p.bump();
				if let (CloseDelim(Paren), _) = p.peek(0) {
					p.add_diag(DiagBuilder2::warning("Superfluous trailing comma").span(sp));
					break;
				} else {
					continue;
				}
			}
			(CloseDelim(Paren), _) => break,
			(x, sp) => {
				p.add_diag(DiagBuilder2::error(format!("Expected , or ) after port declaration, got `{:?}`", x)).span(sp));
				return Err(());
			}
		}
	}

	// Eat the closing parenthesis.
	if !p.try_eat(CloseDelim(Paren)) {
		let (tkn, q) = p.peek(0);
		p.add_diag(DiagBuilder2::error(format!("Expected ) after port list of modport `{}`, got `{:?}`", name, tkn)).span(q));
		return Err(());
	}

	Ok(())
}


/// ```
/// modport_ports_decl:
///   port_direction modport_simple_port {"," modport_simple_port} |
///   ("import"|"export") modport_tf_port {"," modport_tf_port} |
///   "clocking" ident
/// modport_simple_port: ident | "." ident "(" [expr] ")"
/// ```
fn parse_modport_port_decl(p: &mut Parser) -> ReportedResult<()> {
	let (tkn, span) = p.peek(0);

	// Attempt to parse a simple port introduced by one of the port direction
	// keywords.
	if let Some(dir) = as_port_direction(tkn) {
		p.bump();
		loop {
			if p.try_eat(Period) {
				let (name, span) = p.eat_ident("port name")?;
				p.require_reported(OpenDelim(Paren))?;
				// TODO: Parse expression.
				p.require_reported(CloseDelim(Paren))?;
			} else {
				let (name, span) = p.eat_ident("port_name")?;
			}

			// Decide whether we should continue iterating and thus consuming
			// more simple ports. According to the grammar, a comma followed by
			// a keyword indicates a different port declaration, so we abort.
			// Otherwise, if the next item is a comma still, we continue
			// iteration. In all other cases, we assume the port declaration to
			// be done.
			match (p.peek(0).0, p.peek(1).0) {
				(Comma, Keyword(_)) => break,
				(Comma, _) => {
					p.bump();
					continue;
				},
				_ => break,
			}
		}
		return Ok(());
	}

	// TODO: Parse modport_tf_port.

	// Attempt to parse a clocking declaration.
	if p.try_eat(Keyword(Kw::Clocking)) {
		// TODO: Parse modport_clocking_declaration.
		p.add_diag(DiagBuilder2::error("modport clocking declaration not implemented").span(span));
		return Err(());
	}

	// If we've come thus far, none of the above matched.
	p.add_diag(DiagBuilder2::error("Expected port declaration").span(span));
	Err(())
}


pub enum PortDir {
	Input,
	Output,
	Inout,
	Ref,
}

/// Convert a token to the corresponding PortDir. The token may be one of the
/// keywords `input`, `output`, `inout`, or `ref`. Otherwise `None` is returned.
fn as_port_direction(tkn: Token) -> Option<PortDir> {
	match tkn {
		Keyword(Kw::Input) => Some(PortDir::Input),
		Keyword(Kw::Output) => Some(PortDir::Output),
		Keyword(Kw::Inout) => Some(PortDir::Inout),
		Keyword(Kw::Ref) => Some(PortDir::Ref),
		_ => None,
	}
}


fn parse_data_type(p: &mut Parser) -> ReportedResult<()> {
	let (tkn, sp) = p.peek(0);
	match tkn {
		Keyword(Kw::Bit) =>   { p.bump(); return parse_integer_vector_type(p, ()); },
		Keyword(Kw::Logic) => { p.bump(); return parse_integer_vector_type(p, ()); },
		Keyword(Kw::Reg) =>   { p.bump(); return parse_integer_vector_type(p, ()); },
		// TODO: Handle `[` introducing an implicit type.
		// TODO: Handle `signed` and `unsigned` introducing an implicit type.
		_ => (),
	}

	p.add_diag(DiagBuilder2::error(format!("Expected data type, got {:?}", tkn)).span(sp));
	Err(())
}


#[derive(Debug, Clone)]
pub enum Signing {
	None,
	Signed,
	Unsigned,
}

/// Consumes a `signed` or `unsigned` keyword if present.
fn parse_optional_signing(p: &mut Parser) -> Signing {
	match p.peek(0).0 {
		Keyword(Kw::Signed) => {
			p.bump();
			return Signing::Signed;
		},
		Keyword(Kw::Unsigned) => {
			p.bump();
			return Signing::Unsigned;
		},
		_ => return Signing::None,
	}
}


fn parse_optional_dimensions(p: &mut Parser) -> ReportedResult<Vec<Dimensions>> {
	let mut v = Vec::new();
	while let Some(result) = try_dimension(p) {
		match result {
			Ok(d) => v.push(d),
			Err(_) => return Err(()),
		}
	}
	Ok(v)
}


#[derive(Debug, Clone)]
pub enum Dimensions {
	Expr,
	Range,
	Queue,
	Unsized,
	Associative,
}

fn try_dimension(p: &mut Parser) -> Option<ReportedResult<Dimensions>> {
	// Eat the leading opening brackets.
	if !p.try_eat(OpenDelim(Brack)) {
		return None;
	}

	let dim = match p.peek(0).0 {
		CloseDelim(Brack) => {
			p.bump();
			Dimensions::Unsized
		},
		Mul => {
			p.bump();
			Dimensions::Associative
		},
		// TODO: Handle the queue case [$] and [$:<const_expr>]
		_ => {
			// What's left must either be a single constant expression, or a range
			// consisting of two constant expressions.
			let expr = match parse_constant_expr(p) {
				Ok(x) => x,
				Err(_) => {
					p.recover(&[CloseDelim(Brack)], true);
					return Some(Err(()));
				}
			};

			// If the expression is followed by a colon `:`, this is a constant range
			// rather than a constant expression.
			if p.try_eat(Colon) {
				let other = match parse_constant_expr(p) {
					Ok(x) => x,
					Err(_) => {
						p.recover(&[CloseDelim(Brack)], true);
						return Some(Err(()));
					}
				};
				Dimensions::Range
			} else {
				Dimensions::Expr
			}
		}
	};

	// Eat the closing brackets.
	match p.peek(0) {
		(CloseDelim(Brack), _) => {
			p.bump();
			return Some(Ok(dim));
		},
		(tkn, sp) => {
			p.add_diag(DiagBuilder2::error(format!("Expected closing brackets `]` after dimension, got {:?}", tkn)).span(sp));
			return Some(Err(()));
		}
	}
}


fn parse_integer_vector_type(p: &mut Parser, ty: ()) -> ReportedResult<()> {
	let signing = parse_optional_signing(p);
	let dims = parse_optional_dimensions(p)?;
	Ok(())
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
