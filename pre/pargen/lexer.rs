// Copyright (c) 2016 Fabian Schuiki

pub struct Lexer<'a> {
	line: u32,
	column: u32,
	iter: &'a mut Iterator<Item=char>,
	chr: Option<char>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
	Colon,
	Semicolon,
	Pipe,
	Greater,
	LBrace,
	RBrace,
	KwTokenList,
	KwToken,
	KwRoot,
	Ident(String),
	String(String),
}

fn is_ident(c: char) -> bool {
	c == '_' || c.is_alphanumeric()
}

impl<'a> Iterator for Lexer<'a> {
	type Item = Token;

	fn next(&mut self) -> Option<Token> {
		while let Some(c) = self.chr {

			// Skip whitespace.
			if c.is_whitespace() {
				self.eat();
				continue;
			}

			// Skip comments.
			if c == '#' {
				self.eat();
				while let Some(c) = self.chr {
		    		if c == '\n' {
		    			break;
		    		}
			    	self.eat();
			    }
			    continue;
			}

			// Match symbols and identifiers.
			return match c {
			    ':' => { self.eat(); Some(Token::Colon) },
			    ';' => { self.eat(); Some(Token::Semicolon) },
			    '|' => { self.eat(); Some(Token::Pipe) },
			    '>' => { self.eat(); Some(Token::Greater) },
			    '{' => { self.eat(); Some(Token::LBrace) },
			    '}' => { self.eat(); Some(Token::RBrace) },
			    '@' => {
			    	self.eat();
			    	match self.eat_ident().into_boxed_str().as_ref() {
			    		"tokenlist" => Some(Token::KwTokenList),
			    		"token" => Some(Token::KwToken),
			    		"root" => Some(Token::KwRoot),
			    		x => panic!("{}.{}: Unknown keyword @{}", self.line+1, self.column+1, x)
			    	}
			    },
			    '"' => {
			    	self.eat();
			    	let mut buffer = String::new();
					while let Some(c) = self.chr {
						if c == '"' {
							self.eat();
							break;
						}
						buffer.push(c);
						self.eat();
					}
					Some(Token::String(buffer))
			    }
			    x => {
					if is_ident(x) {
						Some(Token::Ident(self.eat_ident()))
					} else {
						panic!("{}.{}: unexpected character '{}'", self.line+1, self.column+1, c)
					}
			    }
			}
		}
		return None
	}
}

impl<'a> Lexer<'a> {
	pub fn new(chars: &'a mut Iterator<Item=char>) -> Self {
		let c = chars.next();
		Lexer {
			line: 0,
			column: 0,
			iter: chars,
			chr: c,
		}
	}

	fn eat(&mut self) {
		if let Some(c) = self.chr {
			if c == '\n' {
				self.line += 1;
				self.column = 0;
			} else {
				self.column += 1;
			}
			self.chr = self.iter.next();
		}
	}

	fn eat_ident(&mut self) -> String {
		let mut buffer = String::new();
		while let Some(c) = self.chr {
			if !is_ident(c) {
				break;
			}
			buffer.push(c);
			self.eat();
		}
		buffer
	}
}
