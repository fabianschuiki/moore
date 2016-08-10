// Copyright (c) 2016 Fabian Schuiki
use std::fs::File;
use lexer::AccumulatingReader;

/// A lexical analyzer for VHDL files.
pub struct Lexer {
	rd: AccumulatingReader,
	eof: bool,
}

pub fn make(filename: &str) -> Lexer {
	let f = File::open(filename).unwrap();
	Lexer {
		rd: AccumulatingReader::new(Box::new(f)),
		eof: false,
	}
}

impl Iterator for Lexer {
	type Item = Token;

	fn next(&mut self) -> Option<Token> {

		// No need to conitnue lexing if we have reached the end of the file.
		if self.eof {
			return None
		}

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
		// characters.
		self.rd.clear();
		let c0 = {
			match self.rd.peek(0) {
				Some(c) => c,
				None => return None
			}
		};
		let c1 = self.rd.peek(1);
		let c2 = self.rd.peek(2);

		// IEEE 1076-2008 15.9 Comments
		if c0 == '-' && c1 == Some('-') {
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

		// IEEE 1076-2008 15.4 Identifiers

		// IEEE 1076-2008 15.4.2 Basic identifiers
		if is_identifier_start(c0) {
			self.rd.consume(1);
			consume_ident(&mut self.rd);

			// IEEE 1076-2008 15.10 Reserved words
			let text = self.rd.to_string();
			return match text.clone().to_lowercase().as_str() {
				"abs" => Some(Token::Keyword(Keyword::Abs)),
				"access" => Some(Token::Keyword(Keyword::Access)),
				"after" => Some(Token::Keyword(Keyword::After)),
				"alias" => Some(Token::Keyword(Keyword::Alias)),
				"all" => Some(Token::Keyword(Keyword::All)),
				"and" => Some(Token::Keyword(Keyword::And)),
				"architecture" => Some(Token::Keyword(Keyword::Architecture)),
				"array" => Some(Token::Keyword(Keyword::Array)),
				"assert" => Some(Token::Keyword(Keyword::Assert)),
				"assume" => Some(Token::Keyword(Keyword::Assume)),
				"assume_guarantee" => Some(Token::Keyword(Keyword::AssumeGuarantee)),
				"attribute" => Some(Token::Keyword(Keyword::Attribute)),
				"begin" => Some(Token::Keyword(Keyword::Begin)),
				"block" => Some(Token::Keyword(Keyword::Block)),
				"body" => Some(Token::Keyword(Keyword::Body)),
				"buffer" => Some(Token::Keyword(Keyword::Buffer)),
				"bus" => Some(Token::Keyword(Keyword::Bus)),
				"case" => Some(Token::Keyword(Keyword::Case)),
				"component" => Some(Token::Keyword(Keyword::Component)),
				"configuration" => Some(Token::Keyword(Keyword::Configuration)),
				"constant" => Some(Token::Keyword(Keyword::Constant)),
				"context" => Some(Token::Keyword(Keyword::Context)),
				"cover" => Some(Token::Keyword(Keyword::Cover)),
				"default" => Some(Token::Keyword(Keyword::Default)),
				"disconnect" => Some(Token::Keyword(Keyword::Disconnect)),
				"downto" => Some(Token::Keyword(Keyword::Downto)),
				"else" => Some(Token::Keyword(Keyword::Else)),
				"elsif" => Some(Token::Keyword(Keyword::Elsif)),
				"end" => Some(Token::Keyword(Keyword::End)),
				"entity" => Some(Token::Keyword(Keyword::Entity)),
				"exit" => Some(Token::Keyword(Keyword::Exit)),
				"fairness" => Some(Token::Keyword(Keyword::Fairness)),
				"file" => Some(Token::Keyword(Keyword::File)),
				"for" => Some(Token::Keyword(Keyword::For)),
				"force" => Some(Token::Keyword(Keyword::Force)),
				"function" => Some(Token::Keyword(Keyword::Function)),
				"generate" => Some(Token::Keyword(Keyword::Generate)),
				"generic" => Some(Token::Keyword(Keyword::Generic)),
				"group" => Some(Token::Keyword(Keyword::Group)),
				"guarded" => Some(Token::Keyword(Keyword::Guarded)),
				"if" => Some(Token::Keyword(Keyword::If)),
				"impure" => Some(Token::Keyword(Keyword::Impure)),
				"in" => Some(Token::Keyword(Keyword::In)),
				"inertial" => Some(Token::Keyword(Keyword::Inertial)),
				"inout" => Some(Token::Keyword(Keyword::Inout)),
				"is" => Some(Token::Keyword(Keyword::Is)),
				"label" => Some(Token::Keyword(Keyword::Label)),
				"library" => Some(Token::Keyword(Keyword::Library)),
				"linkage" => Some(Token::Keyword(Keyword::Linkage)),
				"literal" => Some(Token::Keyword(Keyword::Literal)),
				"loop" => Some(Token::Keyword(Keyword::Loop)),
				"map" => Some(Token::Keyword(Keyword::Map)),
				"mod" => Some(Token::Keyword(Keyword::Mod)),
				"nand" => Some(Token::Keyword(Keyword::Nand)),
				"new" => Some(Token::Keyword(Keyword::New)),
				"next" => Some(Token::Keyword(Keyword::Next)),
				"nor" => Some(Token::Keyword(Keyword::Nor)),
				"not" => Some(Token::Keyword(Keyword::Not)),
				"null" => Some(Token::Keyword(Keyword::Null)),
				"of" => Some(Token::Keyword(Keyword::Of)),
				"on" => Some(Token::Keyword(Keyword::On)),
				"open" => Some(Token::Keyword(Keyword::Open)),
				"or" => Some(Token::Keyword(Keyword::Or)),
				"others" => Some(Token::Keyword(Keyword::Others)),
				"out" => Some(Token::Keyword(Keyword::Out)),
				"package" => Some(Token::Keyword(Keyword::Package)),
				"parameter" => Some(Token::Keyword(Keyword::Parameter)),
				"port" => Some(Token::Keyword(Keyword::Port)),
				"postponed" => Some(Token::Keyword(Keyword::Postponed)),
				"procedure" => Some(Token::Keyword(Keyword::Procedure)),
				"process" => Some(Token::Keyword(Keyword::Process)),
				"property" => Some(Token::Keyword(Keyword::Property)),
				"protected" => Some(Token::Keyword(Keyword::Protected)),
				"pure" => Some(Token::Keyword(Keyword::Pure)),
				"range" => Some(Token::Keyword(Keyword::Range)),
				"record" => Some(Token::Keyword(Keyword::Record)),
				"register" => Some(Token::Keyword(Keyword::Register)),
				"reject" => Some(Token::Keyword(Keyword::Reject)),
				"release" => Some(Token::Keyword(Keyword::Release)),
				"rem" => Some(Token::Keyword(Keyword::Rem)),
				"report" => Some(Token::Keyword(Keyword::Report)),
				"restrict" => Some(Token::Keyword(Keyword::Restrict)),
				"restrict_guarantee" => Some(Token::Keyword(Keyword::RestrictGuarantee)),
				"return" => Some(Token::Keyword(Keyword::Return)),
				"rol" => Some(Token::Keyword(Keyword::Rol)),
				"ror" => Some(Token::Keyword(Keyword::Ror)),
				"select" => Some(Token::Keyword(Keyword::Select)),
				"sequence" => Some(Token::Keyword(Keyword::Sequence)),
				"severity" => Some(Token::Keyword(Keyword::Severity)),
				"shared" => Some(Token::Keyword(Keyword::Shared)),
				"signal" => Some(Token::Keyword(Keyword::Signal)),
				"sla" => Some(Token::Keyword(Keyword::Sla)),
				"sll" => Some(Token::Keyword(Keyword::Sll)),
				"sra" => Some(Token::Keyword(Keyword::Sra)),
				"srl" => Some(Token::Keyword(Keyword::Srl)),
				"strong" => Some(Token::Keyword(Keyword::Strong)),
				"subtype" => Some(Token::Keyword(Keyword::Subtype)),
				"then" => Some(Token::Keyword(Keyword::Then)),
				"to" => Some(Token::Keyword(Keyword::To)),
				"transport" => Some(Token::Keyword(Keyword::Transport)),
				"type" => Some(Token::Keyword(Keyword::Type)),
				"unaffected" => Some(Token::Keyword(Keyword::Unaffected)),
				"units" => Some(Token::Keyword(Keyword::Units)),
				"until" => Some(Token::Keyword(Keyword::Until)),
				"use" => Some(Token::Keyword(Keyword::Use)),
				"variable" => Some(Token::Keyword(Keyword::Variable)),
				"vmode" => Some(Token::Keyword(Keyword::Vmode)),
				"vprop" => Some(Token::Keyword(Keyword::Vprop)),
				"vunit" => Some(Token::Keyword(Keyword::Vunit)),
				"wait" => Some(Token::Keyword(Keyword::Wait)),
				"when" => Some(Token::Keyword(Keyword::When)),
				"while" => Some(Token::Keyword(Keyword::While)),
				"with" => Some(Token::Keyword(Keyword::With)),
				"xnor" => Some(Token::Keyword(Keyword::Xnor)),
				"xor" => Some(Token::Keyword(Keyword::Xor)),

				_ => Some(Token::Ident(text))
			}
		}

		// IEEE 1076-2008 15.4.3 Extended identifiers
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
			return Some(Token::ExtIdent(self.rd.to_string()));
		}

		// IEEE 1076-2008 15.5 Abstract literals
		if c0.is_digit(10) {
			consume_integer(&mut self.rd); // base or integer
			let decimal = self.rd.to_string();
			self.rd.clear();

			match self.rd.peek(0).and_then(|x| x.to_lowercase().next()) {
				// IEEE 1076-2008 15.5.3 Based literals
				Some('#') => {
					let base = u8::from_str_radix(decimal.as_str(), 10).expect("Invalid base in based literal");
					self.rd.consume(1);
					self.rd.clear();

					// Decimal part
					consume_extended_integer(&mut self.rd);
					let decimal = self.rd.to_string();
					self.rd.clear();

					// Fractional part
					let fractional =
						if self.rd.peek(0) == Some('.') {
							consume_extended_integer(&mut self.rd);
							Some(self.rd.to_string())
						} else {
							None
						};
					self.rd.clear();

					// Exponent
					if self.rd.peek(0) != Some('#') {
						panic!("Expected closing # in based literal");
					}
					self.rd.consume(1);
					let exponent = consume_exponent_if_present(&mut self.rd);

					if fractional.is_none() && exponent.is_none() {
						return Some(Token::BasedInteger(base, decimal));
					} else {
						return Some(Token::BasedReal(base, decimal, fractional, exponent));
					}
				},

				// IEE 1076-2008 15.5.2 Decimal literals
				Some('.') => {
					self.rd.consume(1);
					self.rd.clear();
					consume_integer(&mut self.rd);
					let fractional = Some(self.rd.to_string());
					self.rd.clear();
					let exponent = consume_exponent_if_present(&mut self.rd);
					return Some(Token::Real(decimal, fractional, exponent));
				},
				Some('e') => {
					let exponent = consume_exponent_if_present(&mut self.rd);
					return Some(Token::Real(decimal, None, exponent));
				},

				// Integers
				_ => return Some(Token::Integer(decimal)),
			}
		}

		// IEEE 1076-2008 15.6 Character literals
		if c0 == '\'' && c2 == Some('\'') {
			self.rd.consume(3);
			return Some(Token::CharLiteral(self.rd.to_string()));
		}

		// IEEE 1076-2008 15.7 String literals
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
			return Some(Token::StringLiteral(self.rd.to_string()));
		}

		// IEEE 1076-2008 15.3 Lexical elements, separators, delimiters
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

		symbol_match!(
			// 2-character symbols
			'=','>' => Symbol::RArrow;
			'<','=' => Symbol::LArrow;

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
			'=' => Symbol::Equal;

			'+' => Symbol::Add;
			'-' => Symbol::Sub;
			'*' => Symbol::Mul;
			'/' => Symbol::Div;
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


#[derive(Debug)]
pub enum Token {
	Comment(String),
	Ident(String),
	ExtIdent(String),
	Symbol(Symbol),
	Keyword(Keyword),

	// Abstract literals
	Integer(String),
	Real(String, Option<String>, Option<String>),
	BasedInteger(u8, String),
	BasedReal(u8, String, Option<String>, Option<String>),

	// Stirngs
	CharLiteral(String),
	StringLiteral(String),
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

	LArrow,
	RArrow,

	// Punctuation
	Apostrophe,
	Colon,
	Semicolon,
	Period,
	Comma,
	Equal,

	// Operators
	Add,
	Sub,
	Mul,
	Div,
}


#[derive(Debug)]
pub enum Keyword {
	Abs,
	Access,
	After,
	Alias,
	All,
	And,
	Architecture,
	Array,
	Assert,
	Assume,
	AssumeGuarantee,
	Attribute,
	Begin,
	Block,
	Body,
	Buffer,
	Bus,
	Case,
	Component,
	Configuration,
	Constant,
	Context,
	Cover,
	Default,
	Disconnect,
	Downto,
	Else,
	Elsif,
	End,
	Entity,
	Exit,
	Fairness,
	File,
	For,
	Force,
	Function,
	Generate,
	Generic,
	Group,
	Guarded,
	If,
	Impure,
	In,
	Inertial,
	Inout,
	Is,
	Label,
	Library,
	Linkage,
	Literal,
	Loop,
	Map,
	Mod,
	Nand,
	New,
	Next,
	Nor,
	Not,
	Null,
	Of,
	On,
	Open,
	Or,
	Others,
	Out,
	Package,
	Parameter,
	Port,
	Postponed,
	Procedure,
	Process,
	Property,
	Protected,
	Pure,
	Range,
	Record,
	Register,
	Reject,
	Release,
	Rem,
	Report,
	Restrict,
	RestrictGuarantee,
	Return,
	Rol,
	Ror,
	Select,
	Sequence,
	Severity,
	Shared,
	Signal,
	Sla,
	Sll,
	Sra,
	Srl,
	Strong,
	Subtype,
	Then,
	To,
	Transport,
	Type,
	Unaffected,
	Units,
	Until,
	Use,
	Variable,
	Vmode,
	Vprop,
	Vunit,
	Wait,
	When,
	While,
	With,
	Xnor,
	Xor,
}
