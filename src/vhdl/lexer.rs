// Copyright (c) 2016 Fabian Schuiki

//! A lexical analyzer for VHDL files, based on IEEE 1076-2000, section 13.

use std::fs::File;
use lexer::{Reader, AccumulatingReader};
use vhdl::token;
use name::get_name_table;
use errors::{DiagnosticBuilder, DiagResult, DUMMY_HANDLER};
pub use vhdl::token::Token;


/// A lexical analyzer for VHDL files.
pub struct Lexer {
	rd: AccumulatingReader,
}

pub fn make(filename: &str) -> Lexer {
	let f = File::open(filename).unwrap();
	Lexer {
		rd: AccumulatingReader::new(Box::new(f)),
	}
}

impl Lexer {
	/// Returns the next token in the input stream.
	pub fn next_token<'b>(&mut self) -> DiagResult<'b, TokenAndSpan> {
		self.next_token_inner().map(|x| TokenAndSpan { tkn: x, sp: Span { src: 0, lo: 0, hi: 0 }})
	}

	/// Called by next_token to perform the grunt work of token recognition.
	/// The returned token is extended with the associated location in the
	/// source file before it is returned.
	fn next_token_inner<'b>(&mut self) -> DiagResult<'b, Token> {
		loop {
			// Skip whitespace characters.
			while let Some(c) = self.rd.peek(0) {
				if is_whitespace(c) {
					self.rd.consume(1);
					self.rd.clear();
				} else {
					break;
				}
			}

			// Reset the accumulation buffer of the reader and peek the next
			// characters. If we have reached the end of the file, as indicated by
			// the peek(0) being None, return the Eof token.
			self.rd.clear();
			let c0 = {
				match self.rd.peek(0) {
					Some(c) => c,
					None => return Ok(token::Eof)
				}
			};
			let c1 = self.rd.peek(1);
			let c2 = self.rd.peek(2);


			// IEEE 1076-2000 13.9 Comments
			if c0 == '-' && c1 == Some('-') {
				self.rd.consume(2);
				self.rd.clear();
				while let Some(c) = self.rd.peek(0) {
					if c != '\n' {
						self.rd.consume(1);
						self.rd.clear();
					} else {
						break;
					}
				}
				continue;
			}
			if c0 == '/' && c1 == Some('*') {
				self.rd.consume(2);
					self.rd.clear();
				while let Some(c) = self.rd.peek(0) {
					if c != '*' && self.rd.peek(1) != Some('/') {
						self.rd.consume(1);
						self.rd.clear();
					} else {
						break;
					}
				}
				// TODO: Turn this into a proper error.
				if self.rd.peek(0) != Some('*') || self.rd.peek(1) != Some('/') {
					panic!("this should be a diagnostic result");
				}
				self.rd.consume(2);
				self.rd.clear();
				continue;
			}


			let nt = get_name_table();
			let intern_str = |x: String| nt.intern(x.as_str(), true);

			// IEEE 1076-2000 13.3 Identifiers
			// IEEE 1076-2000 13.3.1 Basic Identifiers
			if is_identifier_start(c0) {
				self.rd.consume(1);
				consume_ident(&mut self.rd);
				let name = nt.intern(self.rd.to_string().as_str(), false);
				return Ok(token::Ident(name));
			}

			// IEEE 1076-2000 13.3.2 Extended identifiers
			if c0 == '\\' {
				self.rd.consume(1);
				while let Some(c) = self.rd.peek(0) {
					if c != '\\' {
						self.rd.consume(1);
					} else if self.rd.peek(1) == Some('\\') {
						self.rd.consume(2);
					} else {
						self.rd.consume(1);
						break;
					}
				}
				let name = nt.intern(self.rd.to_string().as_str(), true);
				return Ok(token::Ident(name));
			}


			// IEEE 1076-2000 13.5 Abstract literals
			if c0.is_digit(10) {
				consume_integer(&mut self.rd); // base or integer
				let decimal = self.rd.to_string();
				self.rd.clear();

				match self.rd.peek(0).and_then(|x| x.to_lowercase().next()) {
					// IEEE 1076-2000 13.5.3 Based literals
					Some('#') => {
						// TODO: Turn this into a proper error.
						let base = u8::from_str_radix(decimal.as_str(), 10).expect("Invalid base in based literal");
						self.rd.consume(1);
						self.rd.clear();

						// Decimal part
						consume_extended_integer(&mut self.rd);
						let decimal = nt.intern(self.rd.to_string().as_str(), true);
						self.rd.clear();

						// Fractional part
						let fractional =
							if self.rd.peek(0) == Some('.') {
								consume_extended_integer(&mut self.rd);
								Some(nt.intern(self.rd.to_string().as_str(), true))
							} else {
								None
							};
						self.rd.clear();

						// Exponent
						if self.rd.peek(0) != Some('#') {
							panic!("Expected closing # in based literal");
						}
						self.rd.consume(1);
						let exponent = consume_exponent_if_present(&mut self.rd).map(|x| nt.intern(x.as_str(), true));

						if fractional.is_none() && exponent.is_none() {
							return Ok(token::Literal(token::BasedInteger(base, decimal)));
						} else {
							return Ok(token::Literal(token::BasedReal(base, decimal, fractional, exponent)));
						}
					},

					// IEE 1076-2008 15.5.2 Decimal literals
					Some('.') => {
						self.rd.consume(1);
						self.rd.clear();
						consume_integer(&mut self.rd);
						let fractional = Some(nt.intern(self.rd.to_string().as_str(), true));
						self.rd.clear();
						let exponent = consume_exponent_if_present(&mut self.rd).map(|x| nt.intern(x.as_str(), true));
						return Ok(token::Literal(token::Real(intern_str(decimal), fractional, exponent)));
					},
					Some('e') => {
						let exponent = consume_exponent_if_present(&mut self.rd).map(|x| nt.intern(x.as_str(), true));
						return Ok(token::Literal(token::Real(intern_str(decimal), None, exponent)));
					},

					// Integers
					_ => return Ok(token::Literal(token::Integer(intern_str(decimal)))),
				}
			}

			// IEEE 1076-2000 13.6 Character literals
			if c0 == '\'' && c2 == Some('\'') {
				self.rd.consume(3);
				return Ok(token::Literal(token::Char(intern_str(self.rd.to_string()))));
			}

			// IEEE 1076-2000 13.7 String literals
			if c0 == '"' {
				self.rd.consume(1);
				while let Some(c) = self.rd.peek(0) {
					if c != '"' {
						self.rd.consume(1);
					} else if self.rd.peek(1) == Some('"') {
						self.rd.consume(2);
					} else {
						self.rd.consume(1);
						break;
					}
				}
				return Ok(token::Literal(token::Str(intern_str(self.rd.to_string()))));
			}

			// IEEE 1076-2000 13.3 Lexical elements, separators, delimiters

			// 2-character symbols
			match (c0, c1) {
				('=', Some('>')) => { self.rd.consume(2); return Ok(token::Arrow); },
				('*', Some('*')) => { self.rd.consume(2); return Ok(token::StarStar); },
				(':', Some('=')) => { self.rd.consume(2); return Ok(token::ColonEq); },
				('/', Some('=')) => { self.rd.consume(2); return Ok(token::SlashEq); },
				('>', Some('=')) => { self.rd.consume(2); return Ok(token::GtEq); },
				('<', Some('=')) => { self.rd.consume(2); return Ok(token::LtEq); },
				('<', Some('>')) => { self.rd.consume(2); return Ok(token::LtGt); },
				(_,_) => ()
			}

			// 1-character symbols
			match c0 {
				'('  => { self.rd.consume(1); return Ok(token::OpenDelim(token::Paren)); },
				')'  => { self.rd.consume(1); return Ok(token::CloseDelim(token::Paren)); },
				'['  => { self.rd.consume(1); return Ok(token::OpenDelim(token::Brack)); },
				']'  => { self.rd.consume(1); return Ok(token::CloseDelim(token::Brack)); },
				'{'  => { self.rd.consume(1); return Ok(token::OpenDelim(token::Brace)); },
				'}'  => { self.rd.consume(1); return Ok(token::CloseDelim(token::Brace)); },

				'&'  => { self.rd.consume(1); return Ok(token::Ampersand); },
				'\'' => { self.rd.consume(1); return Ok(token::Apostrophe); },
				':'  => { self.rd.consume(1); return Ok(token::Colon); },
				';'  => { self.rd.consume(1); return Ok(token::Semicolon); },
				'.'  => { self.rd.consume(1); return Ok(token::Period); },
				','  => { self.rd.consume(1); return Ok(token::Comma); },
				'='  => { self.rd.consume(1); return Ok(token::Equal); },
				'+'  => { self.rd.consume(1); return Ok(token::Plus); },
				'-'  => { self.rd.consume(1); return Ok(token::Minus); },
				'*'  => { self.rd.consume(1); return Ok(token::Star); },
				'/'  => { self.rd.consume(1); return Ok(token::Slash); },
				'<'  => { self.rd.consume(1); return Ok(token::Lt); },
				'>'  => { self.rd.consume(1); return Ok(token::Gt); },
				'|'  => { self.rd.consume(1); return Ok(token::Pipe); },
				_ => ()
			}

			// TODO: Explain the following macros and how symbols are matched.
			macro_rules! symbol_pattern {
				($c0:expr, $c1:expr, $c2:expr, $c3:expr) => (($c0, Some($c1), Some($c2), Some($c3)));
				($c0:expr, $c1:expr, $c2:expr) => (($c0, Some($c1), Some($c2), _));
				($c0:expr, $c1:expr) => (($c0, Some($c1), _, _));
				($c0:expr) => (($c0, _, _, _));
			}

			macro_rules! symbol_action {
				($c0:expr, $c1:expr, $c2:expr, $c3:expr, $sym:expr) => ({ self.rd.consume(4); return Some(Token::Symbol($sym)); });
				($c0:expr, $c1:expr, $c2:expr, $sym:expr) => ({ self.rd.consume(3); return Some(Token::Symbol($sym)); });
				($c0:expr, $c1:expr, $sym:expr) => ({ self.rd.consume(2); return Some(Token::Symbol($sym)); });
				($c0:expr, $sym:expr) => ({ self.rd.consume(1); return Some(Token::Symbol($sym)); });
			}

			macro_rules! symbol_match {
				(
					$($($c:tt),+ => $sym:expr;)+
				) => {
					match (c0, c1, c2, self.rd.peek(3)) {
						$(
							symbol_pattern!($($c),*) => symbol_action!($($c),*, $sym),
						)*
						(_,_,_,_) => ()
					}
				}
			}

			// symbol_match!(
			// 	// 2-character symbols
			// 	'=','>' => Symbol::RArrow;
			// 	'<','=' => Symbol::LArrow;

			// 	// 1-character symbols
			// 	'(' => Symbol::LParen;
			// 	')' => Symbol::RParen;
			// 	'[' => Symbol::LBrack;
			// 	']' => Symbol::RBrack;
			// 	'{' => Symbol::LBrace;
			// 	'}' => Symbol::RBrace;

			// 	'\'' => Symbol::Apostrophe;
			// 	':' => Symbol::Colon;
			// 	';' => Symbol::Semicolon;
			// 	'.' => Symbol::Period;
			// 	',' => Symbol::Comma;
			// 	'=' => Symbol::Equal;

			// 	'+' => Symbol::Add;
			// 	'-' => Symbol::Sub;
			// 	'*' => Symbol::Mul;
			// 	'/' => Symbol::Div;
			// );

			// We should never get here unless the input file contains an invalid
			// input character.
			return Err(DiagnosticBuilder{ handler: &DUMMY_HANDLER, message: format!("Invalid input character `{}`.", c0) });
			// panic!("Unknown input token {}", String::from_utf8(self.rd.rem_slice().to_vec()).unwrap());
		}
	}
}

/// Check whether a given byte corresponds to a whitespace.
fn is_whitespace(c: char) -> bool {
	c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == (0xA0 as char)
}

fn is_identifier_start(c: char) -> bool {
	c.is_alphabetic()
}

fn is_identifier(c: char) -> bool {
	c.is_alphanumeric() || c == '_'
}

fn consume_ident(rd: &mut AccumulatingReader) {
	while let Some(c) = rd.peek(0) {
		if is_identifier(c) {
			rd.consume(1);
		} else {
			break;
		}
	}
}

fn consume_integer(rd: &mut AccumulatingReader) {
	while let Some(c) = rd.peek(0) {
		if c.is_digit(10) || c == '_' {
			rd.consume(1);
		} else {
			break;
		}
	}
}

fn consume_extended_integer(rd: &mut AccumulatingReader) {
	while let Some(c) = rd.peek(0) {
		if c.is_alphanumeric() || c == '_' {
			rd.consume(1);
		} else {
			break;
		}
	}
}

fn consume_exponent_if_present(rd: &mut AccumulatingReader) -> Option<String> {
	if rd.peek(0).and_then(|x| x.to_lowercase().next()) == Some('e') {
		rd.consume(1);
		rd.clear();

		if let Some(c) = rd.peek(0) {
			if c == '+' || c == '-' {
				rd.consume(1);
			}
		}
		consume_integer(rd);

		Some(rd.to_string())
	} else {
		None
	}
}



/// A token in conjunction with its location in a source file.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TokenAndSpan {
	pub tkn: Token,
	pub sp: Span,
}


/// A location in a source file, given as byte offsets.
#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub struct Span {
	pub src: u32,
	pub lo: u32,
	pub hi: u32,
}
