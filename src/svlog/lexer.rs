// Copyright (c) 2016 Fabian Schuiki

//! A lexical analyzer for SystemVerilog files, based on IEEE 1800-2009, section
//! 5.

pub use svlog::token::Token;
use errors::*;
use source::*;
use name::get_name_table;
use svlog::cat::CatTokenKind;
use svlog::preproc::*;
use svlog::token::Token::*;
use svlog::token;


type CatTokenAndSpan = (CatTokenKind, Span);
type TokenAndSpan = (Token, Span);


/// A lexical analyzer for SystemVerilog files.
pub struct Lexer<'a> {
	input: Preprocessor<'a>,
	peek: [CatTokenAndSpan; 3],
}

impl<'a> Lexer<'a> {
	pub fn new(input: Preprocessor<'a>) -> Lexer {
		Lexer {
			input: input,
			peek: [(CatTokenKind::Eof, INVALID_SPAN); 3],
		}
	}

	pub fn bump(&mut self) -> DiagResult2<()> {
		self.peek[0] = self.peek[1];
		self.peek[1] = self.peek[2];
		self.peek[2] = match self.input.next() {
			Some(Err(e)) => return Err(e),
			Some(Ok(x)) => x,
			None => (CatTokenKind::Eof, self.peek[1].1),
		};

		Ok(())
	}

	pub fn next_token(&mut self) -> DiagResult2<TokenAndSpan> {
		// Upon the first invocation the peek buffer is still empty. In that
		// case we need to load the first batch of tokens.
		if self.peek[0].0 == CatTokenKind::Eof {
			self.bump();
			self.bump();
			self.bump();
		}

		let name_table = get_name_table();

		loop {
			self.skip_noise();
			println!("peek: {:?}", self.peek);

			match self.peek[0] {
				// A text token either represents an identifier or a number,
				// depending on whether it starts with a digit or a letter. In
				// addition to that, underscores '_' also introduce an
				// identifier.
				// IEEE 1800-2009 5.6 Identifiers
				(CatTokenKind::Text, sp) => {
					let src = sp.source.get_content();
					if sp.iter(&src).next().unwrap().1.is_digit(10) {
						return self.match_number(sp);
					} else {
						let (m, msp) = try!(self.match_ident());
						return Ok((Ident(name_table.intern(&m, true)), msp));
					}
				}
				(CatTokenKind::Symbol('_'), _) => {
					let (m, msp) = try!(self.match_ident());
					return Ok((Ident(name_table.intern(&m, true)), msp));
				}

				// IEEE 1800-2009 5.6.2 Keywords
				// TODO: How are keywords handled? Currently they would be
				// identified by the name table, but that is shared among VHDL
				// and SystemVerilog, which is definitely not what we want.
				// Maybe a special static lookup table for keywords should be
				// used such that we don't rely on the name table at all and
				// have a separate, proper enum variant Kw(...).

				// System tasks and system functions start with the dollar sign
				// '$', after which all regular identifier characters are
				// allowed.
				// IEEE 1800-2009 5.6.3 System tasks and system functions
				(CatTokenKind::Symbol('$'), sp) => {
					self.bump();
					let (m, msp) = try!(self.match_ident());
					return Ok((SysIdent(name_table.intern(&m, true)), Span::union(sp,msp)));
				},

				// Escaped identifiers are introduced with a backslash and last
				// until the next whitespace or newline character.
				// IEEE 1800-2009 5.6.1 Escaped identifiers
				(CatTokenKind::Symbol('\\'), sp) => {
					let mut s = String::new();
					let mut sp = sp;
					loop {
						self.bump();
						if self.peek[0].0 == CatTokenKind::Whitespace || self.peek[0].0 == CatTokenKind::Newline || self.peek[0].0 == CatTokenKind::Eof {
							break;
						}
						sp = Span::union(sp, self.peek[0].1);
						s.push_str(&self.peek[0].1.extract());
					}
					if s.is_empty() {
						return Err(DiagBuilder2::fatal("Expected escaped identifier after backslash '\\'").span(sp));
					}
					return Ok((EscIdent(name_table.intern(&s, true)), sp));
				}

				(CatTokenKind::Eof, sp) => return Ok((Eof, sp)),
				_ => ()
			}

			return Err(DiagBuilder2::fatal(format!("Unknown token {:?}", self.peek[0].0)).span(self.peek[0].1));
		}
	}

	/// Skips all input tokens that are excluded from the language's syntax,
	/// i.e. whitespace, newlines, and comments. Note that during lexical
	/// analysis whitespace may still play a vital role, espceially when parsing
	/// number literals or string constants.
	fn skip_noise(&mut self) -> DiagResult2<()> {
		loop {
			match self.peek[0].0 {
				CatTokenKind::Whitespace | CatTokenKind::Newline | CatTokenKind::Comment => try!(self.bump()),
				_ => return Ok(())
			}
		}
	}

	/// Matches an identifier. This consumes all tokens from the input that when
	/// combined still make up a valid identifier and returns the consumed
	/// characters as a String, alongside the span they covered. In
	/// SystemVerilog upper- and lowercase characters, digits, underscores '_',
	/// and dollar signs '$' are all valid within an identifier.
	fn match_ident(&mut self) -> DiagResult2<(String, Span)> {
		let mut s = String::new();
		let mut sp = self.peek[0].1;
		loop {
			match self.peek[0] {
				(CatTokenKind::Text, this_sp) |
				(CatTokenKind::Symbol('_'), this_sp) |
				(CatTokenKind::Symbol('$'), this_sp) => {
					s.push_str(&this_sp.extract());
					sp = Span::union(sp, this_sp);
					try!(self.bump());
				},
				_ => break,
			}
		}
		assert!(!s.is_empty());
		Ok((s, sp))
	}

	fn match_number(&mut self, first_sp: Span) -> DiagResult2<TokenAndSpan> {
		unimplemented!();
	}
}

impl<'a> Iterator for Lexer<'a> {
	type Item = DiagResult2<TokenAndSpan>;

	fn next(&mut self) -> Option<Self::Item> {
		match self.next_token() {
			Ok((Eof,_)) => None,
			x => Some(x),
		}
	}
}



#[cfg(test)]
mod tests {
	use super::*;
	use source::*;
	use name::*;
	use svlog::preproc::*;
	use svlog::token::Token::*;

	fn check(input: &str, expected: &[Token]) {
		let sm = get_source_manager();
		let source = sm.add("test.sv", input);
		let pp = Preprocessor::new(source, &[]);
		let lexer = Lexer::new(pp);
		let actual: Vec<_> = lexer.map(|x| x.unwrap().0).collect();
		assert_eq!(actual, expected);
	}

	fn name(n: &str) -> Name {
		get_name_table().intern(n, true)
	}

	/// According to IEEE 1800-2009 5.6
	#[test]
	fn idents() {
		check(
			"shiftreg_a busa_index error_condition merge_ab _bus3 n$657",
			&vec![
				Ident(name("shiftreg_a")),
				Ident(name("busa_index")),
				Ident(name("error_condition")),
				Ident(name("merge_ab")),
				Ident(name("_bus3")),
				Ident(name("n$657")),
			]
		);
	}

	/// According to IEEE 1800-2009 5.6.1
	#[test]
	fn esc_idents() {
		check(
			"\\busa+index \\-clock \\***error-condition*** \\net1/\\net2 \\{a,b} \\a*(b+c)",
			&vec![
				EscIdent(name("busa+index")),
				EscIdent(name("-clock")),
				EscIdent(name("***error-condition***")),
				EscIdent(name("net1/\\net2")),
				EscIdent(name("{a,b}")),
				EscIdent(name("a*(b+c)")),
			]
		);
	}

	/// According to IEEE 1800-2009 5.6.3
	#[test]
	fn sys_idents() {
		check(
			"$display $finish $01_ad$as3_",
			&vec![
				SysIdent(name("display")),
				SysIdent(name("finish")),
				SysIdent(name("01_ad$as3_")),
			]
		);
	}
}
