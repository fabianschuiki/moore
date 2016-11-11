// Copyright (c) 2016 Fabian Schuiki

//! A lexical analyzer for SystemVerilog files, based on IEEE 1800-2009, section
//! 5.
//!
//! Getting lexical analysis right for SystemVerilog is very complicated. The
//! language supports many different literals and variations thereof, as well as
//! an entire preprocessor. Currently, the Lexer analyzes the input stream of
//! characters and emits tokens, which are in turn modified by the Preprocessor
//! lexer. This approach is not ideal, since the body of macro definitions needs
//! to be lexically analyzed, separating symbols, whitespace, and alphanumeric
//! characters into tokens. However, number literals shall not yet be processed,
//! since macro substitution can generate new literals (`965``ab123_456).
//! Therefore it seems wise to separate lexical analysis into multiple layers:
//!
//! 1. Read the source file or string and separate it into characters,
//!    whitespaces, comments, symbols, and identifiers, emitting these as
//!    tokens.
//! 2. Perform preprocessing such as macro substitution, resolution of `ifdef
//!    and similar constructs, and including other files.
//! 3. Perform fine-grained lexical analysis, forming complex tokens such as
//!    string and number literals, identifiers, and compound symbols. This is
//!    also where string internalizing should take place, which automatically
//!    classifies identifiers as keywords if appropriate.
//! 4. Regular parsing.
//!
//! This allows for proper preprocessing, since the first step leaves all
//! whitespaces and comments in the token stream, which form part of the syntax
//! of the preprocessor. Also, macro substitution is allowed to generate new
//! compound tokens (e.g. `965``ab123_456) which are then properly classified as
//! number literals (or any other kind of token).

use std::fs::File;
// use std::path::Path;
use lexer::{Reader, AccumulatingReader};
use svlog::token;
use name::get_name_table;
use errors::{DiagnosticBuilder, DiagResult, DUMMY_HANDLER};
pub use svlog::token::Token;

/// A lexical analyzer for SystemVerilog files.
pub struct Lexer {
	rd: AccumulatingReader,
	path: String,
}

pub fn make(filename: &str) -> Lexer {
	let f = File::open(filename).unwrap();
	Lexer {
		rd: AccumulatingReader::new(Box::new(f)),
		path: filename.to_string(),
	}
}

impl Lexer {
	pub fn get_path(&self) -> &str {
		&self.path
	}

	/// Returns the next token in the input stream.
	pub fn next_token<'b>(&mut self) -> DiagResult<'b, TokenAndSpan> {
		self.next_token_inner().map(|x| TokenAndSpan { tkn: x, sp: Span { src: 0, lo: 0, hi: 0 }})
	}

	fn next_token_inner<'b>(&mut self) -> DiagResult<'b, Token> {
		loop {
			// This is the main lexical analysis block. Successfully parsed
			// tokens shall be returned as Ok(...), errors shall be returned as
			// Err(...). If a lexical element has been read for which no token
			// should be emitted, use `continue;` to continue analyzing.


			// IEEE 1800-2009 5.3 White space
			// Skip whitespace characters.
			while let Some(c) = self.rd.peek(0) {
				if is_whitespace(c) {
					self.rd.consume(1);
					self.rd.clear();
				} else {
					break;
				}
			}


			// Reset the accumulation buffer of the reader and peek at the next
			// characters. If we have reached the end of the file, as indicated
			// by peek(0) == None, return the Eof token.
			self.rd.clear();
			let c0 = {
				match self.rd.peek(0) {
					Some(c) => c,
					None => return Ok(token::Eof),
				}
			};
			let c1 = self.rd.peek(1);
			let c2 = self.rd.peek(2);
			let c3 = self.rd.peek(3);


			// IEEE 1800-2009 5.4 Comments
			match (c0,c1) {
				// Single line comments initiated by "//".
				('/', Some('/')) => {
					self.rd.consume(2);
					while let Some(c) = self.rd.peek(0) {
						if c != '\n' {
							self.rd.consume(1);
							self.rd.clear();
						} else {
							break;
						}
					}
					continue; // comments are not emitted as tokens
				},

				// Multi line comments initiated by "/*".
				('/', Some('*')) => {
					while let Some(c) = self.rd.peek(0) {
						if c != '*' || self.rd.peek(1) != Some('/') {
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
					continue; // comments are not emitted as tokens
				},

				(_,_) => ()
			}


			// Get a reference to the current name table into which strings
			// shall be internalized.
			let nt = get_name_table();
			let intern_str = |x: String| nt.intern(x.as_str(), true);

			match c0 {
				// IEEE 1800-2009 5.9 String literals
				// String literals are enclosed by double quotes '"'. A
				// backslash is used to escape special characters. Currently the
				// parsing of such strings is kept to a minimum. However,
				// various special characters can be present in a string and
				// should probably be replaced here during lexical analysis.
				// That is left for a future time though.
				'"' => {
					self.rd.consume(1);
					while let Some(c) = self.rd.peek(0) {
						if c == '\\' {
							self.rd.consume(2);
						} else if c != '"' {
							self.rd.consume(1);
						} else {
							self.rd.consume(1);
							break;
						}
					}
					return Ok(token::Literal(token::Str(intern_str(self.rd.to_string()))));
				},

				// IEEE 1800-2009 5.6.1 Escaped identifiers
				'\\' => {
					self.rd.consume(1);
					self.rd.clear();
					while let Some(c) = self.rd.peek(0) {
						if is_whitespace(c) {
							break;
						} else {
							self.rd.consume(1);
						}
					}
					return Ok(token::Ident(intern_str(self.rd.to_string())));
				}

				// IEEE 1800-2009 5.6.3 System tasks and system functions
				'$' => {
					self.rd.consume(1);
					consume_ident(&mut self.rd);
					let name = intern_str(self.rd.to_string());
					return Ok(token::SysIdent(name));
				},

				// IEEE 1800-2009 5.6.4 Compiler directives
				// Compiler directives behave pretty much like a regular identifier,
				// except for the fact that they are separately marked with a
				// leading backtick '`'.
				'`' => {
					self.rd.consume(1);
					self.rd.clear();
					consume_ident(&mut self.rd);
					let nm = self.rd.to_string();

					if nm == "include" {
						// Skip any whitespace.
						while let Some(c) = self.rd.peek(0) {
							if is_whitespace(c) {
								self.rd.consume(1);
								self.rd.clear();
							} else {
								break;
							}
						}

						// Read the filename, which is either enclosed in
						// double quotes "..." or angle brackets <...>.
						let lquote = self.rd.peek(0);
						let rquote;
						match lquote {
							Some('"') => rquote = '"',
							Some('<') => rquote = '>',
							_ => panic!("expected filename within double quotes \"...\" or angle brackets <...> after `include"),
						}
						self.rd.consume(1);
						self.rd.clear();

						while let Some(c) = self.rd.peek(0) {
							if c == rquote {
								break;
							} else if c == '\n' {
								panic!("expected closing '{}' before newline in `include", rquote);
							} else {
								self.rd.consume(1);
							}
						}
						let filename = self.rd.to_string();

						// Ignore everything up to the next newline.
						while let Some(c) = self.rd.peek(0) {
							if c == '\n' {
								break;
							} else {
								self.rd.consume(1);
								self.rd.clear();
							}
						}

						return Ok(token::Include(intern_str(filename)));
					}

					if nm == "define" {
						// Skip any whitespace.
						while let Some(c) = self.rd.peek(0) {
							if is_whitespace(c) && c != '\n' {
								self.rd.consume(1);
								self.rd.clear();
							} else {
								break;
							}
						}

						// Read the defined name.
						consume_ident(&mut self.rd);
						let name = self.rd.to_string();
						self.rd.clear();

						// Skip any whitespace.
						while let Some(c) = self.rd.peek(0) {
							if is_whitespace(c) && c != '\n' {
								self.rd.consume(1);
								self.rd.clear();
							} else {
								break;
							}
						}

						// If there are opening parenthesis present, parse the
						// macro argument list.
						if self.rd.peek(0) == Some('(') {
							panic!("`define with arguments not implemented");
						}

						// Read the macro body, which lasts until the end of the
						// line.
						while let Some(c) = self.rd.peek(0) {
							if c != '\n' {
								self.rd.consume(1);
							} else {
								break;
							}
						}
						let body = self.rd.to_string();

						return Ok(token::Define(intern_str(name), intern_str(body)));
					}

					return Ok(token::CompDir(intern_str(nm)));
				},

				_ => ()
			}

			// IEEE 1800-2009 5.6 Identifiers, keywords, and system names
			// Catch the regular identifiers.
			if is_identifier_start(c0) {
				self.rd.consume(1);
				consume_ident(&mut self.rd);
				let name = intern_str(self.rd.to_string());
				return Ok(token::Ident(name));
			}


			// IEEE 1800-2009 5.7 Numbers
			// An apostrophe immediately followed by [01xXzZ?] is an unbased,
			// unsized literal.
			if c0 == '\'' && c1.map_or(false, |x| x == '0' || x == '1' || x == 'x' || x == 'X' || x == 'z' || x == 'Z' || x == '?') {
				self.rd.consume(2);
				return Ok(token::Literal(token::UnbasedUnsized(c1.unwrap())));
			}

			// TODO: Numbers generally consist of three tokens, some of which
			// are optional. If whitespaces are allowed in between these tokens,
			// the number parsing process can be moved to the parser, which
			// would make the lexer much simpler.
			if c0.is_digit(10) || c0 == '\'' {
				// Parse the optional size constant or the value itself.
				// TODO: Maybe have first_value be an interned name instead of
				// an optional string.
				let first_value;
				if c0.is_digit(10) {
					consume_decimal(&mut self.rd);
					first_value = Some(self.rd.to_string());
					self.rd.clear();
				} else {
					first_value = None;
				}

				// Parse the base specifier, if present.
				let c = self.rd.peek(0);
				if c != Some('\'') {
					assert!(first_value.is_some());
					return Ok(token::Literal(token::Decimal(intern_str(first_value.unwrap()))));
				}
				self.rd.consume(1);

				// The base specifier may contain a [sS] to indicate a signed
				// value.
				let c = self.rd.peek(0);
				let is_signed =
					if c == Some('s') || c == Some('S') {
						self.rd.consume(1);
						true
					} else {
						false
					};

				// It follows a [dDbBoOhH] to indicate the base of the number.
				let c = self.rd.peek(0);
				if c.is_none() {
					// TODO: Turn this into a proper error message.
					panic!("unexpected eof in the middle of a number literal");
				}
				let base = c.unwrap().to_lowercase().next().unwrap();
				if base != 'd' && base != 'b' && base != 'o' && base != 'h' {
					// TODO: Turn this into a proper error message.
					panic!("invalid base '{}' for number literal, should be [dDbBoOhH]", base);
				}
				self.rd.consume(1);
				self.rd.clear();

				// Consume the rest of the number.
				consume_hexadecimal(&mut self.rd);
				return Ok(token::Literal(token::BasedInteger(
					first_value.map(|x| intern_str(x)),
					base,
					intern_str(self.rd.to_string())
				)));
			}


			// IEEE 1800-2009 5.5 Operators & 11.3 Operators

			// 2-character symbols
			match (c0,c1) {
				('+', Some('=')) => { self.rd.consume(2); return Ok(token::PlusEq); },
				('-', Some('=')) => { self.rd.consume(2); return Ok(token::MinusEq); },
				('*', Some('=')) => { self.rd.consume(2); return Ok(token::StarEq); },
				('/', Some('=')) => { self.rd.consume(2); return Ok(token::SlashEq); },
				('%', Some('=')) => { self.rd.consume(2); return Ok(token::ModEq); },
				('&', Some('=')) => { self.rd.consume(2); return Ok(token::AmpEq); },
				('|', Some('=')) => { self.rd.consume(2); return Ok(token::PipeEq); },
				('^', Some('=')) => { self.rd.consume(2); return Ok(token::CaretEq); },
				('=', Some('=')) => { self.rd.consume(2); return Ok(token::EqEq); },
				('!', Some('=')) => { self.rd.consume(2); return Ok(token::NotEq); },
				('<', Some('=')) => { self.rd.consume(2); return Ok(token::LtEq); },
				('>', Some('=')) => { self.rd.consume(2); return Ok(token::GtEq); },
				('&', Some('&')) => { self.rd.consume(2); return Ok(token::AmpAmp); },
				('~', Some('&')) => { self.rd.consume(2); return Ok(token::TildaAmp); },
				('|', Some('|')) => { self.rd.consume(2); return Ok(token::PipePipe); },
				('*', Some('*')) => { self.rd.consume(2); return Ok(token::StarStar); },
				('<', Some('<')) => { self.rd.consume(2); return Ok(token::LtLt); },
				('>', Some('>')) => { self.rd.consume(2); return Ok(token::GtGt); },
				('+', Some('+')) => { self.rd.consume(2); return Ok(token::PlusPlus); },
				('-', Some('-')) => { self.rd.consume(2); return Ok(token::MinusMinus); },
				('-', Some('>')) => { self.rd.consume(2); return Ok(token::Impl); },
				('^', Some('~')) => { self.rd.consume(2); return Ok(token::CaretTilda); },
				('~', Some('^')) => { self.rd.consume(2); return Ok(token::TildaCaret); },
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

				'#'  => { self.rd.consume(1); return Ok(token::Hash); },
				':'  => { self.rd.consume(1); return Ok(token::Colon); },
				';'  => { self.rd.consume(1); return Ok(token::Semicolon); },
				'.'  => { self.rd.consume(1); return Ok(token::Period); },
				','  => { self.rd.consume(1); return Ok(token::Comma); },
				'='  => { self.rd.consume(1); return Ok(token::Equal); },
				'+'  => { self.rd.consume(1); return Ok(token::Plus); },
				'-'  => { self.rd.consume(1); return Ok(token::Minus); },
				'*'  => { self.rd.consume(1); return Ok(token::Star); },
				'/'  => { self.rd.consume(1); return Ok(token::Slash); },
				'~'  => { self.rd.consume(1); return Ok(token::Tilda); },
				'|'  => { self.rd.consume(1); return Ok(token::Pipe); },
				'<'  => { self.rd.consume(1); return Ok(token::Lt); },
				'>'  => { self.rd.consume(1); return Ok(token::Gt); },
				'!'  => { self.rd.consume(1); return Ok(token::Not); },
				'%'  => { self.rd.consume(1); return Ok(token::Mod); },
				'^'  => { self.rd.consume(1); return Ok(token::Caret); },
				'&'  => { self.rd.consume(1); return Ok(token::Amp); },
				'?'  => { self.rd.consume(1); return Ok(token::Quest); },
				'@'  => { self.rd.consume(1); return Ok(token::At); },
				_ => ()
			}

			return Err(DiagnosticBuilder{ handler: &DUMMY_HANDLER, message: format!("Invalid input character `{}`.", c0) });
		}
	}
}


/// Check whether a character corresponds to a whitespace.
fn is_whitespace(c: char) -> bool {
	c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == (0xA0 as char)
}

/// Check whether a character is a valid initial character for an identifier.
fn is_identifier_start(c: char) -> bool {
	c.is_alphabetic()
}

/// Check whether a character is a valid character for an identifier.
fn is_identifier(c: char) -> bool {
	c.is_alphanumeric() ||  c == '_' || c == '$'
}


/// Consume all characters that are valid in an identifier.
fn consume_ident(rd: &mut AccumulatingReader) {
	while let Some(c) = rd.peek(0) {
		if is_identifier(c) {
			rd.consume(1);
		} else {
			break;
		}
	}
}

/// Consume all characters that are valid for a decimal integer.
fn consume_decimal(rd: &mut AccumulatingReader) {
	while let Some(c) = rd.peek(0) {
		if c.is_digit(10) || c == '_' {
			rd.consume(1);
		} else {
			break;
		}
	}
}

/// Consume all characters that are valid for a hexadecimal integer.
fn consume_hexadecimal(rd: &mut AccumulatingReader) {
	while let Some(c) = rd.peek(0) {
		if c.is_digit(16) || c == '_' {
			rd.consume(1);
		} else {
			break;
		}
	}
}

// impl Iterator for Lexer {
// 	type Item = Token;

// 	fn next(&mut self) -> Option<Token> {

// 		// No need to conitnue lexing if we have reached the end of the file.
// 		if self.eof {
// 			return None
// 		}

// 		// IEEE 1800-2009 5.3
// 		while let Some(c) = self.rd.peek(0) {
// 			if is_whitespace(c) {
// 				self.rd.consume(1);
// 				self.rd.clear();
// 			} else {
// 				break;
// 			}
// 		}

// 		self.rd.clear();
// 		let c0 = {
// 			match self.rd.peek(0) {
// 				Some(c) => c,
// 				None => return None
// 			}
// 		};
// 		let c1 = self.rd.peek(1);

// 		// IEEE 1800-2009 5.4 Comments
// 		if c0 == '/' && c1 == Some('/') {
// 			self.rd.consume(2);
// 			while let Some(c) = self.rd.peek(0) {
// 				if c != '\n' {
// 					self.rd.consume(1);
// 				} else {
// 					break;
// 				}
// 			}
// 			return Some(Token::Comment(self.rd.to_string()));
// 		}
// 		if c0 == '/' && c1 == Some('*') {
// 			self.rd.consume(2);
// 			while let Some(c) = self.rd.peek(0) {
// 				if c != '*' && self.rd.peek(1) != Some('/') {
// 					self.rd.consume(1);
// 				} else {
// 					break;
// 				}
// 			}
// 			// TODO: Turn this into a proper error.
// 			assert!(self.rd.peek(0) == Some('*') && self.rd.peek(1) == Some('/'));
// 			self.rd.consume(2);
// 			return Some(Token::Comment(self.rd.to_string()));
// 		}

// 		// IEEE 1800-2009 5.6.4 Compiler directives
// 		if c0 == '`' {
// 			self.rd.consume(1);
// 			self.consume_ident();
// 			return Some(Token::CompilerDirective(self.rd.to_string()));
// 		}

// 		// IEEE 1800-2009 5.9 String literals
// 		if c0 == '"' {
// 			self.rd.consume(1);
// 			while let Some(c) = self.rd.peek(0) {
// 				if c != '"' {
// 					self.rd.consume(1);
// 				} else {
// 					break;
// 				}
// 			}
// 			// TODO: Turn this into a proper error.
// 			assert!(self.rd.peek(0) == Some('"'));
// 			self.rd.consume(1);
// 			return Some(Token::StringLiteral(self.rd.to_string()));
// 		}

// 		// IEEE 1800-2009 5.6 Identifiers, keywords, and system names
// 		if is_identifier(c0) {
// 			self.rd.consume(1);
// 			self.consume_ident();
// 			return Some(Token::Ident(self.rd.to_string()));
// 		}

// 		// IEEE 1800-2009 5.5 Operators & 11.3 Operators
// 		// TODO: Explain the following macros and how symbols are matched.
// 		macro_rules! symbol_pattern {
// 			($c0:expr, $c1:expr, $c2:expr, $c3:expr) => (($c0, Some($c1), Some($c2), Some($c3)));
// 			($c0:expr, $c1:expr, $c2:expr) => (($c0, Some($c1), Some($c2), _));
// 			($c0:expr, $c1:expr) => (($c0, Some($c1), _, _));
// 			($c0:expr) => (($c0, _, _, _));
// 		}

// 		macro_rules! symbol_action {
// 			($c0:expr, $c1:expr, $c2:expr, $c3:expr, $sym:expr) => ({ self.rd.consume(4); return Some(Token::Symbol($sym)); });
// 			($c0:expr, $c1:expr, $c2:expr, $sym:expr) => ({ self.rd.consume(3); return Some(Token::Symbol($sym)); });
// 			($c0:expr, $c1:expr, $sym:expr) => ({ self.rd.consume(2); return Some(Token::Symbol($sym)); });
// 			($c0:expr, $sym:expr) => ({ self.rd.consume(1); return Some(Token::Symbol($sym)); });
// 		}

// 		macro_rules! symbol_match {
// 			(
// 				$($($c:tt),+ => $sym:expr;)+
// 			) => {
// 				match (c0, c1, self.rd.peek(2), self.rd.peek(3)) {
// 					$(
// 						symbol_pattern!($($c),*) => symbol_action!($($c),*, $sym),
// 					)*
// 					(_,_,_,_) => ()
// 				}
// 			}
// 		}

// 		symbol_match!(
// 			// 4-character symbols
// 			'<','<','<','=' => Symbol::Asasl;

// 			// 3-character symbols
// 			'<','-','>' => Symbol::LogicEquiv;

// 			// 2-character symbols
// 			'+','=' => Symbol::AddAssign;
// 			'-','=' => Symbol::SubAssign;
// 			'*','=' => Symbol::MulAssign;
// 			'/','=' => Symbol::DivAssign;
// 			'%','=' => Symbol::ModAssign;
// 			'&','=' => Symbol::AndAssign;
// 			'|','=' => Symbol::OrAssign;
// 			'^','=' => Symbol::XorAssign;

// 			'*','*' => Symbol::Pow;

// 			'=','=' => Symbol::LogicEq;
// 			'!','=' => Symbol::LogicNeq;
// 			'&','&' => Symbol::LogicAnd;
// 			'|','|' => Symbol::LogicOr;
// 			'-','>' => Symbol::LogicImpl;
// 			'<','=' => Symbol::LogicLe;
// 			'>','=' => Symbol::LogicGe;

// 			'~','&' => Symbol::BitwiseNand;
// 			'~','|' => Symbol::BitwiseNor;
// 			'~','^' => Symbol::BitwiseNxor;
// 			'^','~' => Symbol::BitwiseXnor;

// 			// 1-character symbols
// 			'(' => Symbol::LParen;
// 			')' => Symbol::RParen;
// 			'[' => Symbol::LBrack;
// 			']' => Symbol::RBrack;
// 			'{' => Symbol::LBrace;
// 			'}' => Symbol::RBrace;

// 			'\'' => Symbol::Apostrophe;
// 			':' => Symbol::Colon;
// 			';' => Symbol::Semicolon;
// 			'.' => Symbol::Period;
// 			',' => Symbol::Comma;
// 			'?' => Symbol::Quest;
// 			'@' => Symbol::At;

// 			'=' => Symbol::Assign;

// 			'+' => Symbol::Add;
// 			'-' => Symbol::Sub;
// 			'*' => Symbol::Mul;
// 			'/' => Symbol::Div;
// 			'%' => Symbol::Mod;

// 			'!' => Symbol::LogicNot;
// 			'<' => Symbol::LogicLt;
// 			'>' => Symbol::LogicGt;

// 			'~' => Symbol::BitwiseNot;
// 			'&' => Symbol::BitwiseAnd;
// 			'|' => Symbol::BitwiseOr;
// 			'^' => Symbol::BitwiseXor;


// 			'#' => Symbol::Hashtag;
// 		);

// 		// We should never get here unless the input file contains an invalid
// 		// input character.
// 		panic!("Unknown input token {}", String::from_utf8(self.rd.rem_slice().to_vec()).unwrap());
// 	}
// }



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
