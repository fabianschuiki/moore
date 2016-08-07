// Copyright (c) 2016 Fabian Schuiki
use std::io;
use std::fs::File;
use std::cmp::*;

/// A lexical analyzer for SystemVerilog files.
pub struct Lexer {
	rd: Reader,
	eof: bool,
}

pub fn make(filename: &str) -> Lexer {
	println!("Creating lexer for file {:?}", filename);
	let f = File::open(filename).unwrap();
	Lexer {
		rd: Reader::new(Box::new(f)),
		eof: false,
	}
}

impl Lexer {
	fn consume_ident(&mut self) {
		while let Some(c) = self.rd.peek(0) {
			if is_identifier(c) {
				self.rd.consume(1);
			} else {
				break;
			}
		}
	}
}

impl Iterator for Lexer {
	type Item = Token;

	fn next(&mut self) -> Option<Token> {

		// No need to conitnue lexing if we have reached the end of the file.
		if self.eof {
			return None
		}

		// IEEE 1800-2009 5.3
		while let Some(c) = self.rd.peek(0) {
			if is_whitespace(c) {
				self.rd.consume(1);
				self.rd.clear();
			} else {
				break;
			}
		}

		self.rd.clear();
		let c0 = {
			match self.rd.peek(0) {
				Some(c) => c,
				None => return None
			}
		};
		let c1 = self.rd.peek(1);
		// println!("    Peeked {:?} and {:?}", c0, c1);

		// IEEE 1800-2009 5.4 Comments
		if c0 == '/' && c1 == Some('/') {
			self.rd.consume(2);
			while let Some(c) = self.rd.peek(0) {
				if c != '\n' {
					self.rd.consume(1);
				} else {
					break;
				}
			}
			return Some(Token::Comment(self.rd.to_string()));
		}
		if c0 == '/' && c1 == Some('*') {
			self.rd.consume(2);
			while let Some(c) = self.rd.peek(0) {
				if c != '*' && self.rd.peek(1) != Some('/') {
					self.rd.consume(1);
				} else {
					break;
				}
			}
			// TODO: Turn this into a proper error.
			assert!(self.rd.peek(0) == Some('*') && self.rd.peek(1) == Some('/'));
			self.rd.consume(2);
			return Some(Token::Comment(self.rd.to_string()));
		}

		// IEEE 1800-2009 5.6.4 Compiler directives
		if c0 == '`' {
			self.rd.consume(1);
			self.consume_ident();
			return Some(Token::CompilerDirective(self.rd.to_string()));
		}

		// IEEE 1800-2009 5.9 String literals
		if c0 == '"' {
			self.rd.consume(1);
			while let Some(c) = self.rd.peek(0) {
				if c != '"' {
					self.rd.consume(1);
				} else {
					break;
				}
			}
			// TODO: Turn this into a proper error.
			assert!(self.rd.peek(0) == Some('"'));
			self.rd.consume(1);
			return Some(Token::StringLiteral(self.rd.to_string()));
		}

		// IEEE 1800-2009 5.6 Identifiers, keywords, and system names
		if is_identifier(c0) {
			self.rd.consume(1);
			self.consume_ident();
			return Some(Token::Ident(self.rd.to_string()));
		}

		// IEEE 1800-2009 5.5 Operators & 11.3 Operators
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
				match (c0, c1, self.rd.peek(2), self.rd.peek(3)) {
					$(
						symbol_pattern!($($c),*) => symbol_action!($($c),*, $sym),
					)*
					(_,_,_,_) => ()
				}
			}
		}

		symbol_match!(
			// 4-character symbols
			'<','<','<','=' => Symbol::Asasl;

			// 3-character symbols
			'<','-','>' => Symbol::LogicEquiv;

			// 2-character symbols
			'+','=' => Symbol::AddAssign;
			'-','=' => Symbol::SubAssign;
			'*','=' => Symbol::MulAssign;
			'/','=' => Symbol::DivAssign;
			'%','=' => Symbol::ModAssign;
			'&','=' => Symbol::AndAssign;
			'|','=' => Symbol::OrAssign;
			'^','=' => Symbol::XorAssign;

			'*','*' => Symbol::Pow;

			'=','=' => Symbol::LogicEq;
			'!','=' => Symbol::LogicNeq;
			'&','&' => Symbol::LogicAnd;
			'|','|' => Symbol::LogicOr;
			'-','>' => Symbol::LogicImpl;
			'<','=' => Symbol::LogicLe;
			'>','=' => Symbol::LogicGe;

			'~','&' => Symbol::BitwiseNand;
			'~','|' => Symbol::BitwiseNor;
			'~','^' => Symbol::BitwiseNxor;
			'^','~' => Symbol::BitwiseXnor;

			// 1-character symbols
			'(' => Symbol::LParen;
			')' => Symbol::RParen;
			'[' => Symbol::LBrack;
			']' => Symbol::RBrack;
			'{' => Symbol::LBrace;
			'}' => Symbol::RBrace;

			'\'' => Symbol::Apostrophe;
			':' => Symbol::Colon;
			';' => Symbol::Semicolon;
			'.' => Symbol::Period;
			',' => Symbol::Comma;
			'?' => Symbol::Quest;
			'@' => Symbol::At;

			'=' => Symbol::Assign;

			'+' => Symbol::Add;
			'-' => Symbol::Sub;
			'*' => Symbol::Mul;
			'/' => Symbol::Div;
			'%' => Symbol::Mod;

			'!' => Symbol::LogicNot;
			'<' => Symbol::LogicLt;
			'>' => Symbol::LogicGt;

			'~' => Symbol::BitwiseNot;
			'&' => Symbol::BitwiseAnd;
			'|' => Symbol::BitwiseOr;
			'^' => Symbol::BitwiseXor;


			'#' => Symbol::Hashtag;
		);

		// We should never get here unless the input file contains an invalid
		// input character.
		panic!("Unknown input token {}", String::from_utf8(self.rd.buf[self.rd.base..].to_vec()).unwrap());
	}
}

/// Check whether a given byte corresponds to a whitespace.
fn is_whitespace(c: char) -> bool {
	c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == (0xA0 as char)
}

fn is_identifier(c: char) -> bool {
	(c >= 'A' && c <= 'Z') ||
	(c >= 'a' && c <= 'z') ||
	(c >= '0' && c <= '9') ||
	 c == '_' || c == '$'
}


struct Reader {
	rd: Box<io::Read>,
	buf: Vec<u8>,
	base: usize,
	pos: usize,
	tail: usize,
}

impl Reader {
	fn new(rd: Box<io::Read>) -> Reader {
		Reader {
			rd: rd,
			buf: Vec::new(),
			base: 0,
			pos: 0,
			tail: 0,
		}
	}

	/// Return the value of the byte that is `off` bytes away from the current
	/// position in the input file. If the `off` lies beyond the end of file,
	/// `None` is returned.
	fn peek(&mut self, off: usize) -> Option<char> {
		// If the requested offset lies outside the chunk of the file that is
		// currently in memory, refill the buffer first.
		let idx = self.pos+off;
		if idx >= self.tail {
			self.refill(idx+1)
		}

		// The previous call to refill may move things around in the buffer, so
		// the index needs to be recalculated. If it lies beyond what we were
		// able to read from the file, as indicated by `self.tail`, return
		// `None` to indicate the end of the file.
		let idx = self.pos+off;
		if idx < self.tail {
			Some(self.buf[idx] as char)
		} else {
			None
		}
	}

	/// Grow and fill the internal buffer such that at least min_len characters
	/// are present, or the end of the file has been reached. This function may
	/// shift the buffer contents around, in which case previous buffer indices
	/// become invalid. Recalculate all indices derived from `base`, `pos`, or
	/// `tail` after a call to this function.
	fn refill(&mut self, mut min_len: usize) {
		// Move the buffer contents to the beginning to make more space at the
		// end.
		if self.base > 0 {
			// println!("    Rebasing {} to 0 ({} bytes)", self.base, self.pos-self.base);
			for i in 0..(self.pos-self.base) {
				self.buf[i] = self.buf[self.base+i]
			}
			self.pos -= self.base;
			self.tail -= self.base;
			min_len -= self.base;
			self.base = 0;
		}
		assert!(self.base == 0);

		// Increase the buffer size to make sure the requested min_len can be
		// accomodated.
		let cur_len = self.buf.len();
		if min_len > cur_len {
			let new_len = max(cur_len*2, 32);
			// println!("    Resizing buffer to {} bytes", new_len);
			self.buf.resize(new_len, 0);
		}
		assert!(self.buf.len() >= min_len);

		// Keep reading data until at least min_len bytes are in the buffer.
		// Note that this will usually fill in the entire buffer.
		while min_len > self.tail {
			let nread = {
				let dst = &mut self.buf[self.tail..];
				let nread = self.rd.read(dst).unwrap();
				// println!("    Read {} out of a max of {} bytes", nread, dst.len());
				nread
			};
			if nread == 0 {
				// println!("    Seems like we've hit EOF");
				break;
			}
			self.tail += nread;
			// println!("      {:?}", &self.buf[self.base..self.tail]);
		}
	}

	/// Consume the next `amt` bytes of the input. All consumed bytes since the
	/// last `clear()` can be accessed via `slice()` or `to_string()`.
	fn consume(&mut self, amt: usize) {
		self.pos += amt
	}

	/// Clear the consumed bytes.
	fn clear(&mut self) {
		self.base = self.pos
	}

	/// Return a slice of the consumed bytes.
	fn slice(&self) -> &[u8] {
		&self.buf[self.base .. self.pos]
	}

	/// Convert the consumed bytes to a String.
	fn to_string(&self) -> String {
		// TODO: Don't just unwrap, but handle the case where the input file is
		// not valid UTF8.
		String::from_utf8(self.slice().to_vec()).unwrap()
	}
}


#[derive(Debug)]
pub enum Token {
	Comment(String),
	Ident(String),
	EscapedIdent(String),
	SysName(String),
	StringLiteral(String),
	CompilerDirective(String),
	Symbol(Symbol),
}


#[derive(Debug)]
pub enum Symbol {
	// Grouping
	LParen,
	RParen,
	LBrack,
	RBrack,
	LBrace,
	RBrace,

	// Punctuation
	Apostrophe,
	Colon,
	Semicolon,
	Period,
	Comma,
	Quest,
	At,

	// Operators
	Add,
	Sub,
	Mul,
	Div,
	Pow,
	Mod,

	// Logic operators
	LogicNot,
	LogicEq,
	LogicNeq,
	LogicAnd,
	LogicOr,
	LogicImpl,
	LogicEquiv,
	LogicLt,
	LogicLe,
	LogicGt,
	LogicGe,

	// Bitwise operators
	BitwiseNot,
	BitwiseAnd,
	BitwiseNand,
	BitwiseOr,
	BitwiseNor,
	BitwiseXor,
	BitwiseNxor,
	BitwiseXnor,

	Asasl,
	Hashtag,

	// Assignment operators
	Assign,
	AddAssign,
	SubAssign,
	MulAssign,
	DivAssign,
	ModAssign,
	AndAssign,
	OrAssign,
	XorAssign,
}
