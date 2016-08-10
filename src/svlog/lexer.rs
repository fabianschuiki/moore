// Copyright (c) 2016 Fabian Schuiki
use std::fs::File;
use lexer::AccumulatingReader;

/// A lexical analyzer for SystemVerilog files.
pub struct Lexer {
	rd: AccumulatingReader,
	eof: bool,
}

pub fn make(filename: &str) -> Lexer {
	println!("Creating lexer for file {:?}", filename);
	let f = File::open(filename).unwrap();
	Lexer {
		rd: AccumulatingReader::new(Box::new(f)),
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
		panic!("Unknown input token {}", String::from_utf8(self.rd.rem_slice().to_vec()).unwrap());
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
