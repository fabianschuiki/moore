// Copyright (c) 2016 Fabian Schuiki
use std;
use std::rc::{Rc, Weak};
use std::cell::{RefCell};
use std::cmp::{PartialEq, Eq, PartialOrd, Ord, Ordering};
use std::collections::HashMap;
use std::fmt::Debug;
use std::fs::File;
use std::io::Read;
use std::path::Path;


pub struct Grammar {
	pub rules: Vec<Rc<RefCell<Rule>>>,
}

pub struct Rule {
	pub id: usize,
	pub grammar: Weak<RefCell<Grammar>>,
	pub name: Box<str>,
	pub variants: Vec<Rc<RefCell<Variant>>>,
	pub retype: Option<Box<str>>,
}

pub struct Variant {
	pub id: usize,
	pub rule: Weak<RefCell<Rule>>,
	pub symbols: Vec<RefCell<Symbol>>,
	pub reducer: Option<Box<str>>,
}

#[derive(Clone)]
pub enum Symbol {
	End,
	Unresolved(String),
	Terminal(String),
	NonTerminal(Weak<RefCell<Rule>>),
}


pub fn parse(grammar_path: &Path) -> Rc<RefCell<Grammar>> {

	// Read the entire grammar file into a string.
	let mut src = String::new();
	File::open(grammar_path).unwrap().read_to_string(&mut src).unwrap();

	// Create a lexer for the grammar.
	let mut src_iter = src.chars().into_iter();
	let mut lexer = Lexer::new(&mut src_iter);

	// Create a parser for the grammar and parse the rules.
	let mut parser = Parser::new(&mut lexer);
	let grammar = Rc::new(RefCell::new(Grammar {
		rules: Vec::new(),
	}));

	while !parser.done() {
		parse_rule(&mut parser, &grammar);
	}

	grammar.borrow().link();
	grammar
}


fn parse_rule(parser: &mut Parser, grammar: &Rc<RefCell<Grammar>>) {

	// Rule name.
	let rule_name = match parser.token {
		Some(Token::Ident(ref x)) => x.clone(),
		_ => panic!("expected rule name")
	};
	parser.next();

	let retype = match parser.token {
		Some(Token::String(ref n)) => Some(n.clone().into_boxed_str()),
		_ => None
	};
	if retype.is_some() {
		parser.next();
	}

	let rule_cell = {
		let mut grammar_mut = grammar.borrow_mut();
		let rule = Rc::new(RefCell::new(Rule {
			id: grammar_mut.rules.len(),
			grammar: Rc::downgrade(grammar),
			name: rule_name.into_boxed_str(),
			variants: Vec::new(),
			retype: retype,
		}));
		grammar_mut.rules.push(rule.clone());
		rule
	};
	let mut rule = rule_cell.borrow_mut();

	match parser.token {
		Some(Token::Colon) => parser.next(),
		Some(Token::Semicolon) => { parser.next(); return; },
		ref x => panic!("In rule '{}': Expected ':' or ';' after rule name, got {:?} instead", rule.name, x)
	};

	// Variants.
	loop {
		let mut variant = Variant {
			id: rule.variants.len(),
			rule: Rc::downgrade(&rule_cell),
			symbols: Vec::new(),
			reducer: None,
		};

		loop {
			variant.symbols.push(match parser.token {
				Some(Token::Ident(ref x)) => RefCell::new(Symbol::Unresolved(x.clone())),
				_ => break,
			});
			parser.next();
		}

		// Parse the reduction rule name.
		match parser.token {
			Some(Token::Greater) => {
				parser.next();
				match parser.token {
					Some(Token::Ident(ref x)) => variant.reducer = Some(x.clone().into_boxed_str()),
					ref x => panic!("In rule '{}': Expected reducer name after '>', got {:?} instead", rule.name, x)
				};
				parser.next();
			},
			_ => (),
		}

		// Add the variant to the rule.
		rule.variants.push(Rc::new(RefCell::new(variant)));

		// Decide whether to continue or finish this rule.
	    match parser.token {
	    	Some(Token::Pipe) => { parser.next(); continue; },
	    	Some(Token::Semicolon) => { parser.next(); break; },
			ref x => panic!("In rule '{}': Expected terminal, non-terminal, '|', or ';', got {:?} instead", rule.name, x)
	    }
	}
}


struct Lexer<'a> {
	line: u32,
	column: u32,
	iter: &'a mut Iterator<Item=char>,
	chr: Option<char>,
}

#[derive(Debug, PartialEq, Clone)]
enum Token {
	Colon,
	Semicolon,
	Pipe,
	Greater,
	Ident(String),
	String(String),
	Terminal(String),
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
			    '@' => { self.eat(); Some(Token::Terminal(self.eat_ident())) },
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
	fn new(chars: &'a mut Iterator<Item=char>) -> Self {
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


struct Parser<'a> {
	lexer: &'a mut Lexer<'a>,
	token: Option<Token>
}

impl<'a> Parser<'a> {
	fn new(lexer: &'a mut Lexer<'a>) -> Self {
		let tkn = lexer.next();
		Parser {
			lexer: lexer,
			token: tkn,
		}
	}

	fn next(&mut self) {
		self.token = self.lexer.next();
	}

	fn done(&mut self) -> bool {
		self.token.is_none()
	}
}



impl Grammar {
	pub fn link(&self) {
		// Build a rule lookup table.
		let rule_table = {
			let mut tbl = HashMap::<Box<str>, Weak<RefCell<Rule>>>::new();
			for rule in &self.rules {
				tbl.insert(rule.borrow().name.clone(), Rc::downgrade(&rule));
			}
			tbl
		};

		// Link the symbols.
		let mut id = 0;
		for rule_cell in &self.rules {
			let mut rule = rule_cell.borrow_mut();
			rule.id = id;
			id += 1;

			for variant_cell in &rule.variants {
				let mut variant = variant_cell.borrow_mut();
				variant.id = id;
				id += 1;

				for symbol in &variant.symbols {
					let replacement =
						if let Symbol::Unresolved(ref name) = *symbol.borrow() {
							if let Some(rule) = rule_table.get(name.as_str()) {
								Symbol::NonTerminal(rule.clone())
							} else {
								Symbol::Terminal(name.clone())
							}
						} else {
							continue;
						};
					*symbol.borrow_mut() = replacement;
				}
			}
		}
	}

	pub fn get_root(&self) -> &Rc<RefCell<Rule>> {
		return &self.rules[0];
	}

	pub fn get_pattern(&self, name: &str) -> String {
		let mut s = String::from("Token::");
		match name {
			"IDENT" => s.push_str("Ident(_)"),
			"LPAREN" => s.push_str("Symbol(Symbol::LParen)"),
			"RPAREN" => s.push_str("Symbol(Symbol::RParen)"),
			"LBRACE" => s.push_str("Symbol(Symbol::LBrace)"),
			"RBRACE" => s.push_str("Symbol(Symbol::RBrace)"),
			"LBRACK" => s.push_str("Symbol(Symbol::LBrack)"),
			"RBRACK" => s.push_str("Symbol(Symbol::RBrack)"),
			"SUFFIX" => s.push_str("Ident(_)"),
			"SEMICOLON"|"COMMA"|"COLON"|"PERIOD" => {
				s.push_str("Symbol(Symbol::");
				let mut it = name.chars();
				if let Some(c) = it.next() {
					s.push(c.to_uppercase().next().unwrap());
				}
				while let Some(c) = it.next() {
					s.push(c.to_lowercase().next().unwrap());
				}
				s.push_str(")");
			},
			_ => {
				s.push_str("Keyword(Keyword::");
				let mut it = name.chars();
				if let Some(c) = it.next() {
					s.push(c.to_uppercase().next().unwrap());
				}
				while let Some(c) = it.next() {
					s.push(c.to_lowercase().next().unwrap());
				}
				s.push_str(")");
			}
		}
		return s
	}
}


impl Rule {
	pub fn get_name(&self) -> &str {
		self.name.as_ref()
	}

	pub fn get_id(&self) -> usize {
		self.id
	}

	pub fn get_variants(&self) -> &Vec<Rc<RefCell<Variant>>> {
		&self.variants
	}
}


impl Variant {
	pub fn get_symbols(&self) -> &Vec<RefCell<Symbol>> {
		&self.symbols
	}
}


impl Symbol {
	fn cardinal(&self) -> u32 {
		match *self {
			Symbol::End => 0,
			Symbol::Unresolved(_) => 1,
			Symbol::Terminal(_) => 2,
			Symbol::NonTerminal(_) => 3,
		}
	}

	fn get_name(&self) -> &String {
		match *self {
			Symbol::Unresolved(ref name) => name,
			Symbol::Terminal(ref name) => name,
			_ => panic!("{:?} has no name", self),
		}
	}

	fn get_rule(&self) -> Rc<RefCell<Rule>> {
		match *self {
			Symbol::NonTerminal(ref rule) => rule.upgrade().unwrap(),
			_ => panic!("{:?} has no rule", self),
		}
	}
}



impl Ord for Rule {
	fn cmp(&self, other: &Self) -> Ordering {
		self.id.cmp(&other.id)
	}
}

impl PartialOrd for Rule {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl PartialEq for Rule {
	fn eq(&self, other: &Self) -> bool {
		self.id == other.id
	}
}

impl Eq for Rule {}



impl Ord for Variant {
	fn cmp(&self, other: &Self) -> Ordering {
		self.id.cmp(&other.id)
	}
}

impl PartialOrd for Variant {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl PartialEq for Variant {
	fn eq(&self, other: &Self) -> bool {
		self.id == other.id
	}
}

impl Eq for Variant {}



impl Ord for Symbol {
	fn cmp(&self, other: &Self) -> Ordering {
		let o = self.cardinal().cmp(&other.cardinal());
		if o == Ordering::Equal {
			match *self {
				Symbol::Unresolved(ref name) => name.cmp(other.get_name()),
				Symbol::Terminal(ref name) => name.cmp(other.get_name()),
				Symbol::NonTerminal(ref rule) => rule.upgrade().unwrap().cmp(&other.get_rule()),
				_ => o,
			}
		} else {
			o
		}
	}
}

impl PartialOrd for Symbol {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl PartialEq for Symbol {
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other) == Ordering::Equal
	}
}

impl Eq for Symbol {}



impl Debug for Grammar {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		for rule in &self.rules {
			try!(write!(f, "{:?}\n", *rule.borrow()));
		}
		Ok(())
	}
}

impl Debug for Rule {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		try!(write!(f, "{}", self.name));
		let mut sep = ':';
		for variant in &self.variants {
			try!(write!(f, "\n    {} {:?}", sep, *variant.borrow()));
			sep = '|';
		}
		write!(f, " ;")
	}
}

impl Debug for Variant {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		let mut it = self.symbols.iter();
		if let Some(sym) = it.next() {
			try!(sym.borrow().fmt(f));
			for sym in it {
				try!(write!(f, " "));
				try!(sym.borrow().fmt(f));
			}
		}
		Ok(())
	}
}

impl Debug for Symbol {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			&Symbol::Unresolved(ref x) => write!(f, "<?'{}'>", x),
			&Symbol::Terminal(ref x) => write!(f, "{}", x),
			&Symbol::NonTerminal(ref rc) => {
				let r = rc.upgrade().unwrap();
				return write!(f, "{}", r.borrow().name);
			},
			&Symbol::End => write!(f, "$"),
		}
	}
}
