// Copyright (c) 2016 Fabian Schuiki

//! The categorizing lexer. Tokenizes an input stream of characters, yielding a
//! stream of newline, whitespace, comment, symbol, and text tokens.
//!
//! # Example
//! ```
//! let input = "Löwe 老虎 Léopard\n";
//! let mut cat = Cat::new(Box::new(input.char_indices()));
//! let tokens: Vec<_> = cat.collect();
//! ```

use source::*;
use errors::*;
use lexer::{Reader, Lexer};
pub use self::CatTokenKind::*;



/// The categorizing lexer. Divides an input stream of characters (unicode) into
/// coarse groups of tokens. These include whitespace, comments, symbols, and
/// text. The strings contained in the emitted tokens can be concatenated to
/// arrive at the original file, i.e. no information is lost.
pub struct Cat<'a> {
	iter: Box<CharIter<'a>>,
	last: usize,
	chars: (Option<char>, Option<char>),
	indices: (usize, usize),
}

impl<'a> Cat<'a> {
	/// Create a new categorizing lexer from an `CharIter` iterator.
	pub fn new(mut iter: Box<CharIter<'a>>) -> Cat<'a> {
		let last = iter.size_hint().1.expect("Iterator must provide upper bounds");
		let c0 = iter.next();
		let c1 = iter.next();
		Cat {
			iter: iter,
			last: last,
			chars: (
				c0.map(|x| x.1),
				c1.map(|x| x.1)
			),
			indices: (
				c0.map(|x| x.0).unwrap_or(last),
				c1.map(|x| x.0).unwrap_or(last)
			),
		}
	}

	/// Advance to the next character in the input stream.
	fn bump(&mut self) {
		let c = self.iter.next();
		self.chars = (self.chars.1, c.map(|x| x.1));
		self.indices = (self.indices.1, c.map(|x| x.0).unwrap_or(self.last));
	}
}

impl<'a> Iterator for Cat<'a> {
	type Item = CatToken;

	fn next(&mut self) -> Option<Self::Item> {
		match self.chars {
			(None, _) => None,

			// Newlines
			(Some('\n'), _) => {
				let t = CatToken(Newline, self.indices.0, self.indices.1);
				self.bump();
				Some(t)
			}

			// Whitespace characters
			(Some(c), _) if is_whitespace(c) => {
				let p0 = self.indices.0;
				while let (Some(c), _) = self.chars {
					if !is_whitespace(c) {
						break;
					}
					self.bump();
				}
				Some(CatToken(Whitespace, p0, self.indices.0))
			}

			// IEEE 1800-2009 5.4 Comments
			// Consume single-line comments initiated by "//".
			(Some('/'), Some('/')) => {
				let p0 = self.indices.0;
				while let (Some(c), _) = self.chars {
					if c == '\n' {
						break;
					}
					self.bump();
				}
				Some(CatToken(Comment, p0, self.indices.0))
			}

			// Consume multi-line comments inititated by "/*".
			(Some('/'), Some('*')) => {
				let p0 = self.indices.0;
				while let (Some(c0), Some(c1)) = self.chars {
					if c0 == '*' && c1 == '/' {
						self.bump();
						self.bump();
						break;
					}
					self.bump();
				}
				Some(CatToken(Comment, p0, self.indices.0))
			}

			// Consume symbols.
			// IEEE 1800-2009 5.5 Operators & 11.3 Operators
			(Some(c), _) if is_symbol(c) => {
				let t = CatToken(Symbol(c), self.indices.0, self.indices.1);
				self.bump();
				Some(t)
			}

			// Consume text.
			(Some(c), _) => {
				let p0 = self.indices.0;
				while let (Some(c), _) = self.chars {
					if c == '\n' || is_whitespace(c) || is_symbol(c) {
						break;
					}
					self.bump();
				}
				Some(CatToken(Text, p0, self.indices.0))
			}
		}
	}
}

/// Check whether the given character is considered a whitespace in
/// SystemVerilog.
fn is_whitespace(c: char) -> bool {
	c == ' ' || c == '\t' || c == '\r' || c == (0xA0 as char)
}

/// Check whether the given character is considered a symbol in SystemVerilog.
fn is_symbol(c: char) -> bool {
	match c {
		'(' |
		')' |
		'[' |
		']' |
		'{' |
		'}' |
		'#' |
		':' |
		';' |
		'.' |
		',' |
		'=' |
		'+' |
		'-' |
		'*' |
		'/' |
		'~' |
		'|' |
		'<' |
		'>' |
		'!' |
		'%' |
		'^' |
		'&' |
		'?' |
		'\'' |
		'"' |
		'`' |
		'@' => true,
		_ => false,
	}
}



/// A token emitted by the categorizing lexer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CatToken(pub CatTokenKind, pub usize, pub usize);

/// The different kinds of tokens the categorizing lexer can emit.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CatTokenKind {
	Newline,
	Whitespace,
	Comment,
	Symbol(char),
	Text,
}



#[cfg(test)]
mod tests {
	use super::*;
	use errors::*;
	use lexer::{Lexer, StringReader};

	fn lex(input: &str) -> Vec<CatToken> {
		Cat::new(Box::new(input.char_indices())).collect()
	}

	#[test]
	fn empty() {
		assert_eq!(lex(""), vec![]);
	}

	#[test]
	fn non_empty() {
		assert_eq!(lex("Löwe 老虎 Léopard\n"), vec![
			CatToken(Text, 0, 5),
			CatToken(Whitespace, 5, 6),
			CatToken(Text, 6, 12),
			CatToken(Whitespace, 12, 13),
			CatToken(Text, 13, 21),
			CatToken(Newline, 21, 22),
		]);
	}
}
