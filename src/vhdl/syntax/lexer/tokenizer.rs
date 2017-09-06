// Copyright (c) 2017 Fabian Schuiki

use moore_common::grind::{Grinder, Lookahead};
use moore_common::errors::*;
use moore_common::source::*;
use moore_common::name::*;
use syntax::lexer::bundler::Bundle;
use syntax::lexer::token::*;


/// A grinder that combines character bundles into lexical tokens. This is the
/// last stage of lexical analysis.
pub struct Tokenizer<T: Grinder> {
	inner: Lookahead<T>,
}

impl<T: Grinder> Tokenizer<T> where T: Grinder<Item=Option<Spanned<Bundle>>, Error=DiagBuilder2> {
	/// Create a new bundler.
	pub fn new<I>(inner: I) -> Tokenizer<T> where I: Into<Lookahead<T>> {
		Tokenizer { inner: inner.into() }
	}

	/// Returns the next bundle in the input for which `is_significant` is true.
	fn next_significant(&mut self) -> Option<Spanned<Bundle>> {
		while let Some(v) = self.inner.next() {
			if v.value.is_significant() {
				return Some(v);
			}
		}
		None
	}

	/// Parses a bit string literal with an optional size already parsed. These
	/// are of the form `<size>[B|O|X|D|UB|UO|UX|SB|SO|SX]"<bits>"`.
	fn parse_bit_string_literal(&mut self, int: Option<Spanned<Name>>, base: Spanned<String>, mut value: Spanned<String>) -> Spanned<Token> {
		let (int, mut span) = match int {
			Some(Spanned{ value, span }) => (Some(value), span),
			None => (None, base.span),
		};
		span.end = value.span.end;

		// Parse the base.
		let base = match base.value.as_str() {
			"B"  => BitStringBase::B,
			"O"  => BitStringBase::O,
			"X"  => BitStringBase::X,
			"D"  => BitStringBase::D,
			"UB" => BitStringBase::UB,
			"UO" => BitStringBase::UO,
			"UX" => BitStringBase::UX,
			"SB" => BitStringBase::SB,
			"SO" => BitStringBase::SO,
			"SX" => BitStringBase::SX,
			b => {
				self.emit(
					DiagBuilder2::error(format!("`{}` is not a valid base for a bit string literal", b))
					.span(base.span)
					.add_note("Valid bases are B, O, X, UB, UO, UX, SB, SO, SX, D")
				);
				BitStringBase::B
			}
		};

		// Parse the value.
		let mut parsed_value = String::new();
		for c in value.value.drain(..) {
			if !c.is_whitespace() {
				if c != '_' {
					parsed_value.push(c);
				}
			} else {
				self.emit(
					DiagBuilder2::error(format!("Character `{}` may not appear in a bit string literal", c))
					.span(value.span)
				);
			}
		}
		let value = get_name_table().intern(&parsed_value, true);

		Spanned::new(Lit(Literal::BitString(int, base, value)), span)
	}


	/// Parse an integer, i.e. a sequence of digits with optional intermittent
	/// underscores '_'.
	fn parse_integer(&mut self, mut s: String, mut sp: Span) -> Spanned<Name> {
		loop {
			match self.inner.next() {
				Some(Spanned{ value: Bundle::Digits(n), span }) => {
					s.push_str(&n);
					sp.end = span.end;
				},
				Some(Spanned{ value: Bundle::Special('_'), .. }) => (),
				n => {
					self.inner.undo(n);
					break;
				}
			}
		}
		Spanned::new(get_name_table().intern(&s, true), sp)
	}


	/// Parse an based integer, i.e. a sequence of letters and digits with
	/// optional intermittent underscores '_'.
	fn parse_based_integer(&mut self) -> Spanned<Name> {
		let (mut s, mut sp) = match self.inner.next() {
			Some(Spanned{ value: Bundle::Letters(n), span }) |
			Some(Spanned{ value: Bundle::Digits(n), span }) => (n, span),
			Some(n) => {
				let sp = n.span.begin().into();
				self.emit(DiagBuilder2::error("Expected digits or letters").span(sp));
				self.inner.undo(Some(n));
				return Spanned::new(get_name_table().intern("", true), sp);
			},
			None => {
				self.emit(DiagBuilder2::error("Expected digits or letters"));
				self.inner.undo(None);
				return Spanned::new(get_name_table().intern("", true), INVALID_SPAN);
			}
		};
		loop {
			match self.inner.next() {
				Some(Spanned{ value: Bundle::Letters(n), span }) |
				Some(Spanned{ value: Bundle::Digits(n), span }) => {
					s.push_str(&n);
					sp.end = span.end;
				},
				Some(Spanned{ value: Bundle::Special('_'), .. }) => (),
				n => {
					self.inner.undo(n);
					break;
				}
			}
		}
		Spanned::new(get_name_table().intern(&s, true), sp)
	}

	/// Try to parse an exponent, introduced by a `E` character.
	fn try_exponent(&mut self) -> Option<Spanned<Exponent>> {
		match self.inner.next() {
			Some(Spanned{ value: Bundle::Letters(ref l), span: mut sp }) if l == "e" || l == "E" => {
				let mut n = self.inner.next();
				let sign = match n {
					Some(Spanned{ value: Bundle::Special('+'), .. }) => {
						n = self.inner.next();
						ExponentSign::Positive
					}
					Some(Spanned{ value: Bundle::Special('-'), .. }) => {
						n = self.inner.next();
						ExponentSign::Negative
					}
					_ => ExponentSign::Positive
				};
				match n {
					Some(Spanned{ value: Bundle::Digits(s), span }) => {
						let int = self.parse_integer(s, span);
						sp.end = int.span.end;
						Some(Spanned::new(Exponent(sign, int.value), sp))
					}
					n => {
						self.emit(
							DiagBuilder2::error(format!("Expected exponent after `{}`", l))
							.span(sp)
						);
						self.inner.undo(n);
						None
					}
				}
			},
			n => {
				self.inner.undo(n);
				None
			}
		}
	}

	/// Parse any of the symbols in the language. `c0` comes from a
	/// `Bundle::Special` that has already been parsed.
	fn parse_symbol(&mut self, c0: char, mut span: Span) -> Option<Spanned<Token>> {
		let n1 = self.inner.next();
		let n2 = self.inner.next();

		// Try to parse a three-character symbol.
		if let (
				&Some(Spanned{ value: Bundle::Special(c1), .. }),
				&Some(Spanned{ value: Bundle::Special(c2), span: sp })
			) = (&n1, &n2) {
			if let Some(tkn) = match (c0, c1, c2) {
				('?','/','=') => Some(MatchNeq),
				('?','<','=') => Some(MatchLeq),
				('?','>','=') => Some(MatchGeq),
				_ => None
			} {
				span.expand(sp);
				return Some(Spanned::new(tkn, span));
			}
		}
		self.inner.undo(n2);

		// Try to parse a two-character symbol.
		if let &Some(Spanned{ value: Bundle::Special(c1), span: sp }) = &n1 {
			if let Some(tkn) = match (c0, c1) {
				('=','>') => Some(Arrow),
				('?','?') => Some(Condition),
				('<','>') => Some(LtGt),
				(':','=') => Some(VarAssign),
				('<','<') => Some(Lshift),
				('>','>') => Some(Rshift),
				('/','=') => Some(Neq),
				('<','=') => Some(Leq),
				('>','=') => Some(Geq),
				('?','=') => Some(MatchEq),
				('?','<') => Some(MatchLt),
				('?','>') => Some(MatchGt),
				('*','*') => Some(Pow),
				_ => None
			} {
				span.expand(sp);
				return Some(Spanned::new(tkn, span));
			}
		}
		self.inner.undo(n1);

		// Try to parse a one-character symbol.
		if let Some(tkn) = match c0 {
			'('  => Some(OpenDelim(Paren)),
			')'  => Some(CloseDelim(Paren)),
			'['  => Some(OpenDelim(Brack)),
			']'  => Some(CloseDelim(Brack)),
			'.'  => Some(Period),
			','  => Some(Comma),
			':'  => Some(Colon),
			';'  => Some(Semicolon),
			'\'' => Some(Apostrophe),
			'&'  => Some(Ampersand),
			'='  => Some(Eq),
			'<'  => Some(Lt),
			'>'  => Some(Gt),
			'+'  => Some(Add),
			'-'  => Some(Sub),
			'*'  => Some(Mul),
			'/'  => Some(Div),
			'|'  => Some(Pipe),
			'?'  => Some(Qmark),
			_ => None
		} {
			return Some(Spanned::new(tkn, span));
		}

		// If we get here, we parsed something which is allowed in VHDL source
		// text, but is not a valid symbol on its own.
		self.emit(DiagBuilder2::error(format!("`{}` is not a valid symbol", c0)).span(span));
		None
	}
}

impl<T> Grinder for Tokenizer<T> where T: Grinder<Item=Option<Spanned<Bundle>>, Error=DiagBuilder2> {
	type Item = Option<Spanned<Token>>;
	type Error = DiagBuilder2;

	fn emit(&mut self, err: Self::Error) {
		self.inner.emit(err);
	}

	fn next(&mut self) -> Self::Item {
		let b = match self.next_significant() {
			Some(v) => v,
			None => return None,
		};

		match b.value {
			Bundle::Letters(mut s) => {
				let mut m = self.inner.next();
				if let Some(Spanned{ value: Bundle::StringLiteral(v), span }) = m {
					// If the letters are immediately followed by a string literal,
					// parse this as a bit string literal.
					Some(self.parse_bit_string_literal(None, Spanned::new(s,b.span), Spanned::new(v,span)))
				} else {
					// Parse a basic identifier.
					let mut sp = b.span;
					loop {
						match m {
							Some(Spanned{ value: Bundle::Letters(n), span }) |
							Some(Spanned{ value: Bundle::Digits(n), span }) => {
								s.push_str(&n);
								sp.end = span.end;
								m = self.inner.next();
							}
							Some(Spanned{ value: Bundle::Special('_'), span }) => {
								s.push('_');
								sp.end = span.end;
								m = self.inner.next();
							}
							n => {
								self.inner.undo(n);
								break;
							}
						}
					}

					// See if this identifier is a keyword.
					Some(Spanned::new(
						if let Some(kw) = find_keyword(&s) {
							Keyword(kw)
						} else {
							Ident(get_name_table().intern(&s, false))
						},
						sp,
					))
				}
			}

			Bundle::ExtendedIdent(s) => Some(Spanned::new(
				Ident(get_name_table().intern(&s, true)),
				b.span
			)),

			Bundle::Digits(s) => {
				// Parse the integer and decide how to continue.
				let int = self.parse_integer(s, b.span);
				match (self.inner.next(), self.inner.next()) {

					// If the integer is followed by some letters and a string
					// literal, interpret this as a bit string literal.
					(
						Some(Spanned{ value: Bundle::Letters(b), span: sp1 }),
						Some(Spanned{ value: Bundle::StringLiteral(s), span: sp2 }),
					) => {
						Some(self.parse_bit_string_literal(Some(int), Spanned::new(b,sp1), Spanned::new(s,sp2)))
					}

					// If the integer is followed by a period '.', parse the
					// following fractional part.
					(
						Some(Spanned{ value: Bundle::Special('.'), .. }),
						Some(Spanned{ value: Bundle::Digits(s), span }),
					) => {
						let frac = self.parse_integer(s, span);
						let exp = self.try_exponent();
						let mut sp = int.span;
						let exp = match exp {
							Some(Spanned{ value, span }) => {
								sp.end = span.end;
								Some(value)
							}
							_ => {
								sp.end = frac.span.end;
								None
							}
						};
						Some(Spanned::new(Lit(Literal::Abstract(None, int.value, Some(frac.value), exp)), sp))
					}

					// If the integer is followed by a hashtag '#', parse this
					// as a based literal.
					(Some(Spanned{ value: Bundle::Special('#'), .. }), n) => {
						self.inner.undo(n);
						let base = int;
						let int = self.parse_based_integer();
						let mut sp = Span::union(base.span, int.span);

						// Parse the optional fractional part.
						let n = self.inner.next();
						let frac = if let Some(Spanned{ value: Bundle::Special('.'), .. }) = n {
							let f = self.parse_based_integer();
							sp.expand(f.span);
							Some(f.value)
						} else {
							self.inner.undo(n);
							None
						};

						// Match the second `#`.
						match self.inner.next() {
							Some(Spanned{ value: Bundle::Special('#'), span }) => {
								sp.expand(span);
							}
							n => {
								self.emit(
									DiagBuilder2::error("Expected `#` after digits of based literal")
									.span(sp.end())
								);
								self.inner.undo(n);
							}
						}

						// Parse the optional exponent.
						let exp = match self.try_exponent() {
							Some(Spanned{ value, span }) => {
								sp.end = span.end;
								Some(value)
							}
							_ => None
						};

						Some(Spanned::new(Lit(Literal::Abstract(Some(base.value), int.value, frac, exp)), sp))
					}

					// Otherwise, simply check for an exponent and we're done.
					(n,m) => {
						self.inner.undo(m);
						self.inner.undo(n);
						let exp = self.try_exponent();
						let mut sp = int.span;
						let exp = match exp {
							Some(Spanned{ value, span }) => {
								sp.end = span.end;
								Some(value)
							}
							_ => {
								sp.end = int.span.end;
								None
							}
						};
						Some(Spanned::new(Lit(Literal::Abstract(None, int.value, None, exp)), sp))
					}
				}
			}

			Bundle::StringLiteral(s) => Some(Spanned::new(
				Lit(Literal::String(get_name_table().intern(&s, true))),
				b.span,
			)),

			Bundle::BitLiteral(c) => Some(Spanned::new(
				Lit(Literal::Char(c)),
				b.span,
			)),

			Bundle::Special(c0) => self.parse_symbol(c0, b.span),
			Bundle::Space | Bundle::Comment => unreachable!(),
		}
	}
}
