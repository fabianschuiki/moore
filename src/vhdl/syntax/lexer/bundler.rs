// Copyright (c) 2017 Fabian Schuiki

use moore_common::grind::{Grinder, Lookahead};
use moore_common::errors::DiagBuilder2;
use moore_common::source::*;
use lexer::categorizer::Category;


/// A grinder that bundles up categorized characters into groups and converts
/// spaces and comments into single tokens, dropping any information about their
/// content. String and bit string literals are formed here as well.
pub struct Bundler<T: Grinder> {
	inner: Lookahead<T>,
	src: Source,
}

impl<T: Grinder> Bundler<T> {
	/// Create a new bundler.
	pub fn new<I>(inner: I, src: Source) -> Bundler<T> where I: Into<Lookahead<T>> {
		Bundler { inner: inner.into(), src: src }
	}
}

impl<T> Grinder for Bundler<T> where T: Grinder<Item=Option<(usize, char, u8, Category)>, Error=DiagBuilder2> {
	type Item = Option<Spanned<Bundle>>;
	type Error = DiagBuilder2;

	fn emit(&mut self, err: Self::Error) {
		self.inner.emit(err);
	}

	fn next(&mut self) -> Self::Item {
		let (begin, c, sz, cat) = match self.inner.next() {
			Some(v) => v,
			None => return None,
		};
		let mut sp = Span::new(self.src, begin, begin + sz as usize);

		// Handle single-line comments.
		if c == '-' {
			if let Some((_, '-', _, _)) = *self.inner.lookahead(0) {
				self.inner.next();
				while let &Some((offset, d, sz, _)) = self.inner.lookahead(0) {
					if d == '\n' {
						break;
					} else {
						sp.end = offset + sz as usize;
						self.inner.next();
					}
				}
				return Some(Spanned::new(Bundle::Comment, sp));
			}
		}

		// Handle multi-line comments.
		if c == '/' {
			if let Some((_, '*', _, _)) = *self.inner.lookahead(0) {
				self.inner.next();
				let mut p0 = None;
				let mut p1 = None;
				while let Some((offset, d, sz, _)) = *self.inner.lookahead(0) {
					if p0 == Some('*') && p1 == Some('/') {
						break;
					} else {
						p0 = p1;
						p1 = Some(d);
						sp.end = offset + sz as usize;
						self.inner.next();
					}
				}
				return Some(Spanned::new(Bundle::Comment, sp));
			}
		}

		// Handle bit string literals.
		if c == '\'' {
			if let Some((offset, '\'', sz, _)) = *self.inner.lookahead(1) {
				let (_, b, _, _) = self.inner.next().unwrap();
				self.inner.next();
				sp.end = offset + sz as usize;
				return Some(Spanned::new(Bundle::BitLiteral(b), sp));
			}
		}

		// Handle string literals.
		if c == '"' {
			let mut s = String::new();
			while let Some((offset, d, sz, _)) = self.inner.next() {
				sp.end = offset + sz as usize;
				if d == '"' {
					if let Some((_, '"', _, _)) = *self.inner.lookahead(0) {
						s.push('"');
						self.inner.next();
					} else {
						break;
					}
				} else if d == '\n' {
					self.emit(DiagBuilder2::error("String literal must not contain line breaks.")
						.span(sp.end())
						.add_note("Use string concatenation (e.g. \"abc\" & \"def\") to break strings across lines"));
				} else {
					s.push(d);
				}
			}
			return Some(Spanned::new(Bundle::StringLiteral(s), sp));
		}

		// Handle extended identifiers.
		if c == '\\' {
			let mut s = String::new();
			s.push(c);
			while let Some((offset, d, sz, _)) = self.inner.next() {
				sp.end = offset + sz as usize;
				if d == '\\' {
					s.push('\\');
					if let Some((_, '\\', _, _)) = *self.inner.lookahead(0) {
						self.inner.next();
					} else {
						break;
					}
				} else if d == '\n' {
					self.emit(DiagBuilder2::error("Extended identifier must not contain line breaks.")
						.span(sp.end()));
				} else {
					s.push(d);
				}
			}
			return Some(Spanned::new(Bundle::ExtendedIdent(s), sp));
		}

		// Bundle up the remaining characters.
		match cat {

			// If the character is a letter or digit, aggregate all following
			// characters of the same kind into a string.
			Category::Letter | Category::Digit => {
				let mut s = String::new();
				s.push(c);
				while let &Some((offset, d, sz, c)) = self.inner.lookahead(0) {
					if c == cat {
						s.push(d);
						sp.end = offset + sz as usize;
						self.inner.next();
					} else {
						break;
					}
				}
				Some(Spanned::new(
					match cat {
						Category::Letter => Bundle::Letters(s),
						Category::Digit  => Bundle::Digits(s),
						_ => unreachable!(),
					},
					sp
				))
			}

			// If the character is a space, consume adjacent spaces and emit a
			// token that covers the correct span, but does not contain the
			// spaces themselves.
			Category::Space => {
				while let Some((offset, _, sz, Category::Space)) = *self.inner.lookahead(0) {
					sp.end = offset + sz as usize;
					self.inner.next();
				}
				Some(Spanned::new(Bundle::Space, sp))
			}

			// Emit special characters as 1-char bundles.
			Category::Special => Some(Spanned::new(Bundle::Special(c), sp)),

			// Throw errors for invalid characters.
			Category::Other => {
				self.emit(DiagBuilder2::error(format!("Character `{}` not allowed in VHDL source text", c)).span(sp));
				None
			}
		}
	}
}

/// A bundle of characters. These are the most fundamental groups of characters
/// as per the VHDL standard. Lexical analysis will aggregate one or more of
/// these into more meaningful tokens.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bundle {
	Letters(String),
	Digits(String),
	Special(char),
	StringLiteral(String),
	BitLiteral(char),
	ExtendedIdent(String),
	Space,
	Comment,
}

impl Bundle {
	/// Check whether the bundle has syntactic significance, i.e. is not a
	/// comment or space.
	pub fn is_significant(&self) -> bool {
		match *self {
			Bundle::Space | Bundle::Comment => false,
			_ => true,
		}
	}
}
