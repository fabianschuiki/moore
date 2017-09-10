// Copyright (c) 2017 Fabian Schuiki

//! This module implements a basic parser that accepts tokens from the VHDL
//! lexer and emits errors back to it.

use std::collections::VecDeque;
use moore_common::grind::Grinder;
use moore_common::source::*;
use moore_common::errors::*;
use syntax::lexer::Lexer;
use syntax::lexer::token::Token;
use syntax::parser::TokenStream;


pub struct BasicParser<T> where T: Grinder<Item=Option<u8>, Error=DiagBuilder2> {
	input: Lexer<T>,
	queue: VecDeque<Spanned<Token>>,
	last_span: Span,
	severity: Severity,
	consumed: usize,
}


impl<T> TokenStream<Token> for BasicParser<T> where T: Grinder<Item=Option<u8>, Error=DiagBuilder2> {
	fn peek(&mut self, offset: usize) -> Spanned<Token> {
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
		if let Some(Spanned{ value, span }) = self.queue.pop_front() {
			assert!(value != Token::Eof);
			self.last_span = span;
			self.consumed += 1;
		}
	}

	fn consumed(&self) -> usize {
		self.consumed
	}

	fn last_span(&self) -> Span {
		self.last_span
	}

	fn emit(&mut self, diag: DiagBuilder2) {
		use std::cmp::max;
		self.severity = max(self.severity, diag.get_severity());
		self.input.emit(diag);
	}

	fn severity(&self) -> Severity {
		self.severity
	}
}


impl<T> BasicParser<T> where T: Grinder<Item=Option<u8>, Error=DiagBuilder2> {
	/// Create a new parser which consumes input from the given lexer.
	pub fn new(input: Lexer<T>) -> BasicParser<T> {
		BasicParser {
			input: input,
			queue: VecDeque::new(),
			last_span: INVALID_SPAN,
			severity: Severity::Note,
			consumed: 0,
		}
	}

	/// Ensure that either the end of file has been reached, or at least
	/// `min_tokens` tokens are in the queue.
	fn ensure_queue_filled(&mut self, min_tokens: usize) {
		if let Some(&Spanned{ value: Token::Eof, .. }) = self.queue.back() {
			return;
		}
		while self.queue.len() <= min_tokens {
			match self.input.next() {
				Some(t) => self.queue.push_back(t),
				None => {
					self.queue.push_back(Spanned::new(Token::Eof, self.last_span.end().into()));
					break;
				}
			}
		}
	}
}
