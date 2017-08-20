// Copyright (c) 2017 Fabian Schuiki

use std;
use std::fmt::Display;
use std::marker::PhantomData;
use moore_common::errors::*;
use moore_common::name::*;
use moore_common::source::*;
use syntax::lexer::token::*;
use syntax::parser::rules::{Parser, Reported, Recovered, ReportedResult, RecoveredResult};


/// A predicate that matches on the current position of a token stream.
pub trait Predicate<P: Parser>: Display {
	/// Match the predicate against the current position of the parser.
	fn matches(&mut self, &mut P) -> bool;
	/// Skip tokens in the parser until the predicate matches. Optionally also
	/// consume the tokens that make up the predicate.
	fn recover(&mut self, &mut P, consume: bool);
}

impl<P> Predicate<P> for Token where P: Parser {
	fn matches(&mut self, p: &mut P) -> bool {
		p.peek(0).value == *self
	}

	fn recover(&mut self, p: &mut P, consume: bool) {
		recover(p, &[*self], consume)
	}
}


/// A function predicate.
struct FuncPredicate<P: Parser, M: FnMut(&mut P) -> bool, R: FnMut(&mut P, bool)> {
	match_func: M,
	recover_func: R,
	desc: &'static str,
	_marker: PhantomData<P>,
}

impl<P,M,R> Predicate<P> for FuncPredicate<P,M,R>
where P: Parser, M: FnMut(&mut P) -> bool, R: FnMut(&mut P, bool) {
	fn matches(&mut self, p: &mut P) -> bool {
		(self.match_func)(p)
	}

	fn recover(&mut self, p: &mut P, consume: bool) {
		(self.recover_func)(p, consume)
	}
}

impl<P,M,R> Display for FuncPredicate<P,M,R>
where P: Parser, M: FnMut(&mut P) -> bool, R: FnMut(&mut P, bool) {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.desc)
	}
}


// TODO: Document this!
pub fn recover<P: Parser>(p: &mut P, term: &[Token], eat_term: bool) {
	let mut stack = Vec::new();
	loop {
		let Spanned{ value: tkn, span: sp } = p.peek(0);
		if stack.is_empty() {
			for t in term {
				if *t == tkn {
					if eat_term {
						p.skip();
					}
					return;
				}
			}
		}

		// p.emit(
		// 	DiagBuilder2::note("Skipped during recovery")
		// 	.span(sp)
		// );

		match tkn {
			OpenDelim(x) => stack.push(x),
			CloseDelim(x) => {
				if let Some(open) = stack.pop() {
					if open != x {
						p.emit(
							DiagBuilder2::fatal(format!("Found closing {} which is not the complement to the previous opening {}", CloseDelim(x), OpenDelim(open)))
							.span(sp)
						);
						break;
					}
				} else {
					p.emit(
						DiagBuilder2::fatal(format!("Found closing {} without an earlier opening {}", CloseDelim(x), OpenDelim(x)))
						.span(sp)
					);
					break;
				}
			}
			Eof => break,
			_ => (),
		}
		p.skip();
	}
}


/// Apply a parser and if it fails, recover to one of a list of tokens. This
/// turns reported into recovered errors.
pub fn recovered<P: Parser, R, F>(p: &mut P, term: &[Token], eat_term: bool, mut parse: F) -> RecoveredResult<R>
where F: FnMut(&mut P) -> Result<R, Reported> {
	match parse(p) {
		Ok(x) => Ok(x),
		Err(Reported) => {
			recover(p, term, eat_term);
			Err(Recovered)
		}
	}
}


/// Consume a token if it is present, do nothing otherwise.
pub fn accept<P: Parser>(p: &mut P, expect: Token) -> bool {
	if p.peek(0).value == expect {
		p.bump();
		true
	} else {
		false
	}
}


/// Consume a specific token, or emit an error if the next token in the stream
/// does not match the expected one.
pub fn require<P: Parser>(p: &mut P, expect: Token) -> ReportedResult<()> {
	let Spanned{ value: actual, span } = p.peek(0);
	if actual == expect {
		p.bump();
		Ok(())
	} else {
		p.emit(
			DiagBuilder2::error(format!("Expected {}, but found {} instead", expect, actual))
			.span(span)
		);
		Err(Reported)
	}
}


/// Repeatedly apply a parser until it returns `None`.
pub fn repeat<P: Parser, R, F, E>(p: &mut P, mut parse: F) -> Result<Vec<R>, E>
where F: FnMut(&mut P) -> Result<Option<R>, E> {
	let mut v = Vec::new();
	while p.peek(0).value != Eof {
		match parse(p)? {
			Some(x) => v.push(x),
			None => break,
		}
	}
	Ok(v)
}


/// Parse a list of items separated with a specific token, until a terminator
/// oktne has been reached. The terminator is not consumed.
pub fn separated<P: Parser, M, R, F, T>(
		p: &mut P,
		sep: Token,
		mut term: T,
		msg: &M,
		mut parse: F
	) -> RecoveredResult<Vec<R>> where
	F: FnMut(&mut P) -> ReportedResult<R>,
	T: Predicate<P>,
	M: Display + ?Sized {

	let mut v = Vec::new();
	while !p.is_fatal() && p.peek(0).value != Eof && !term.matches(p) {
		// Parse the item. If the parser fails, recover to the terminator and
		// abort.
		match parse(p) {
			Ok(x) => v.push(x),
			Err(_) => {
				term.recover(p, false);
				return Err(Recovered);
			}
		}

		// Try to match the terminator. If it does not, consume a separator and
		// catch the case where the separator is immediately followed by the
		// terminator (superfluous separator).
		if term.matches(p) {
			break;
		} else if accept(p, sep) {
			if term.matches(p) {
				let q = p.last_span();
				p.emit(
					DiagBuilder2::warning(format!("Superfluous trailing {}", sep))
					.span(q)
				);
				break;
			}
		} else {
			let sp = p.peek(0).span;
			p.emit(
				DiagBuilder2::error(format!("Expected {} or {} after {}", sep, term, msg))
				.span(sp)
			);
			term.recover(p, false);
			return Err(Recovered);
		}
	}
	Ok(v)
}


/// Parse a non-empty list. See `separated` for details.
pub fn separated_nonempty<P: Parser, M, R, F, T>(
		p: &mut P,
		sep: Token,
		term: T,
		msg: &M,
		parse: F
	) -> RecoveredResult<Vec<R>> where
	F: FnMut(&mut P) -> ReportedResult<R>,
	T: Predicate<P>,
	M: Display + ?Sized {

	let q = p.peek(0).span;
	let v = separated(p, sep, term, msg, parse)?;
	if v.is_empty() {
		p.emit(
			DiagBuilder2::error(format!("Expected at least one {}", msg))
			.span(q)
		);
		Err(Recovered)
	} else {
		Ok(v)
	}
}


/// Parses the opening delimiter, calls the `inner` function, and parses the
/// closing delimiter. Properly recovers to and including the closing
/// delimiter if the `inner` function throws an error.
pub fn flanked<P: Parser, R, F>(p: &mut P, delim: DelimToken, mut inner: F) -> RecoveredResult<R>
where F: FnMut(&mut P) -> ReportedResult<R> {
	require(p, OpenDelim(delim)).map_err(|_| Recovered)?;
	match inner(p) {
		Ok(r) => {
			match require(p, CloseDelim(delim)) {
				Ok(_) => Ok(r),
				Err(Reported) => {
					recover(p, &[CloseDelim(delim)], true);
					Err(Recovered)
				}
			}
		}
		Err(Reported) => {
			recover(p, &[CloseDelim(delim)], true);
			Err(Recovered)
		}
	}
}


/// If the opening delimiter is present, consumes it, calls the `inner`
/// function, and parses the closing delimiter. Properly recovers to and
/// including the closing delimiter if the `inner` function throws an error.
/// If the opening delimiter is not present, returns `None`.
pub fn try_flanked<P: Parser, R, F>(p: &mut P, delim: DelimToken, inner: F) -> RecoveredResult<Option<R>>
where F: FnMut(&mut P) -> ReportedResult<R> {
	if p.peek(0).value == OpenDelim(delim) {
		flanked(p, delim, inner).map(|r| Some(r))
	} else {
		Ok(None)
	}
}


/// Parse an identifier.
pub fn parse_ident<P: Parser, M: Display>(p: &mut P, msg: M) -> ReportedResult<Spanned<Name>> {
	let Spanned{ value, span } = p.peek(0);
	match value {
		Ident(n) => {
			p.bump();
			Ok(Spanned::new(n, span))
		}
		wrong => {
			p.emit(
				DiagBuilder2::error(format!("Expected {}, but found {} instead", msg, wrong))
				.span(span)
			);
			Err(Reported)
		}
	}
}
