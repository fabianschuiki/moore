// Copyright (c) 2016 Fabian Schuiki
use std;
use std::rc::Rc;
use std::cell::{RefCell};
use std::fs::File;
use std::io::Read;
use std::path::Path;
use pargen::lexer::*;
// use pargen::new_grammar;
use pargen::grammar::{self, GrammarBuilder, RuleBuilder};


/// A simple wrapper around a lexer that keeps one token of lookahead.
struct Parser<'a> {
	lexer: &'a mut Lexer<'a>,
	token: Option<Token>,
	// grammar: new_grammar::Grammar,
	// grammar: GrammarBuilder,
}

impl<'a> Parser<'a> {
	fn new(lexer: &'a mut Lexer<'a>) -> Self {
		let tkn = lexer.next();
		Parser {
			lexer: lexer,
			token: tkn,
			// grammar: new_grammar::Grammar::new(),
			// grammar: GrammarBuilder::new(),
		}
	}

	fn next(&mut self) {
		self.token = self.lexer.next();
	}

	/// Return the current token and advance the parser.
	fn consume(&mut self) -> Option<Token> {
		std::mem::replace(&mut self.token, self.lexer.next())
	}

	/// Discard the current token given it matches the required one. Panics if
	/// the tokens don't match.
	fn require(&mut self, token: Token) {
		match self.consume() {
			Some(tkn) => {
				if tkn != token {
					panic!("Expected {:?}, got {:?} instead", token, tkn);
				}
			},
			None => panic!("Expected {:?}, reached end of file instead", token)
		}
	}

	/// If the current token is equivalent to the requested one, consume the
	/// token and return true. Otherwise return false.
	fn accept(&mut self, token: Token) -> bool {
		if self.token == Some(token) {
			self.next();
			true
		} else {
			false
		}
	}

	/// If the current token is a string, return the string and advance the
	/// parser. Otherwise return None.
	fn accept_string(&mut self) -> Option<Box<str>> {
		let tkn = std::mem::replace(&mut self.token, None);
		if let Some(Token::String(s)) = tkn {
			self.token = self.lexer.next();
			Some(s.into_boxed_str())
		} else {
			self.token = tkn;
			None
		}
	}


	/// Parses an entire grammar.
	fn parse(&mut self, grammar: &mut GrammarBuilder) {
		// let mut grammar = GrammarBuilder::new();
		loop {
			match self.consume() {
				Some(Token::KwTokenList) => self.parse_token_list(grammar),
				Some(Token::KwToken) => self.parse_token(grammar),
				Some(Token::KwRoot) => self.parse_root(grammar),
				Some(Token::Ident(name)) => self.parse_rule(name.into_boxed_str(), grammar),
				Some(x) => panic!("Expected statement, got {:?} instead", x),
				None => break
			}
		}

		println!("builder = {:?}", grammar);
		// self.grammar.link();
		// println!("parsed {:?}", self.grammar);
		// println!("Parsed token types: {:?}", self.token_types);
	}


	/// Parses a `@tokenlist <string> { <ident> <string>; ... }` statement.
	fn parse_token_list(&mut self, grammar: &mut GrammarBuilder) {
		// Parse the pattern for the token list which contains a '@' symbol that
		// will be replaced by a token-specific string.
		let pattern = match self.consume() {
			Some(Token::String(p)) => p,
			x => panic!("Expected pattern string, got {:?} instead", x)
		};

		// Parse the token declarations.
		self.require(Token::LBrace);
		loop {
			match self.consume() {
				Some(Token::Ident(name)) => {
					let repl = match self.consume() {
						Some(Token::String(s)) => s,
						x => panic!("Expected pattern substitution string for token {}, got {:?} instead", name, x)
					};
					self.require(Token::Semicolon);
					grammar.add_terminal(
						name.into_boxed_str(),
						pattern.replace("@", repl.as_ref()).into_boxed_str()
					);
				},
				Some(Token::RBrace) => break,
				x => panic!("Expected token name or '}}', got {:?} instead", x)
			}
		}
	}


	/// Parses a `@token <ident> <string>;` statement.
	fn parse_token(&mut self, grammar: &mut GrammarBuilder) {
		// Parse the name of the token that will be used throughout the grammar.
		let name = match self.consume() {
			Some(Token::Ident(n)) => n,
			x => panic!("Expected token name, got {:?} instead", x)
		};

		// Parse the substitution string that will be used for the token in the
		// generated Rust code.
		let repl = match self.consume() {
			Some(Token::String(s)) => s,
			x => panic!("Expected type string for token {}, got {:?} instead", name, x)
		};

		self.require(Token::Semicolon);
		grammar.add_terminal(name.into_boxed_str(), repl.into_boxed_str());
	}


	/// Parses a `@root <ident>;` statement.
	fn parse_root(&mut self, grammar: &mut GrammarBuilder) {
		// Parse the name of the root rule.
		let name = match self.consume() {
			Some(Token::Ident(n)) => n,
			x => panic!("Expected root rule name, got {:?} instead", x)
		};

		self.require(Token::Semicolon);
		println!("root rule is {}", name);
		grammar.set_root(name.into_boxed_str());
	}


	fn parse_rule<'b>(&mut self, name: Box<str>, grammar: &'b mut GrammarBuilder) {
		// let mut rule = new_grammar::Rule::new(name);
		let mut rule = grammar.new_rule(name);

		// Parse the reduction type of this rule which will be used in the
		// reduce function synthesized in Rust.
		if let Some(rt) = self.accept_string() {
			rule.set_reduced_type(rt);
		}

		// Parse the individual variants.
		loop {
			match self.consume() {
				Some(Token::Colon) | Some(Token::Pipe) => self.parse_variant(&mut rule),
				Some(Token::Semicolon) => break,
				x => panic!("Expected ':', '|', or ';', got {:?} instead", x)
			}
		}

		// self.grammar.add_rule(rule);
		rule.build();
	}


	// fn parse_variant(&mut self, rule: &mut new_grammar::Rule) {
	fn parse_variant(&mut self, rule: &mut RuleBuilder) {
		// let mut var = new_grammar::Variant::new();
		let mut var = rule.new_variant();

		// Parse the symbols of this variant.
		loop {
			let tkn = std::mem::replace(&mut self.token, None);
			match tkn {
				Some(Token::Ident(ident)) => {
					// var.add_symbol(new_grammar::Symbol::Unresolved(ident.into_boxed_str()));
					var.add_symbol(ident.into_boxed_str());
					self.token = self.lexer.next();
				},
				_ => {
					self.token = tkn;
					break;
				}
			}
		}

		// Parse the reduction function name.
		if self.accept(Token::Greater) {
			match self.consume() {
				Some(Token::Ident(ident)) => var.set_reducer_fn(ident.into_boxed_str()),
				x => panic!("Expected reduction function name, got {:?} instead", x)
			}
		}

		// self.grammar.add_variant(var, rule);
		var.build();
	}
}


pub fn parse(grammar_path: &Path) -> Box<grammar::Grammar> {

	// Read the entire grammar file into a string.
	let mut src = String::new();
	File::open(grammar_path).unwrap().read_to_string(&mut src).unwrap();

	// Create a lexer for the grammar.
	let mut src_iter = src.chars().into_iter();
	let mut lexer = Lexer::new(&mut src_iter);

	// Create a parser for the grammar and parse the rules.
	let mut parser = Parser::new(&mut lexer);
	// let grammar = Rc::new(RefCell::new(grammar::Grammar {
	// 	rules: Vec::new(),
	// }));

	let mut gb = GrammarBuilder::new();
	parser.parse(&mut gb);

	// grammar.borrow().link();
	// grammar
	gb.build()
}


// fn parse_rule(parser: &mut Parser, grammar: &Rc<RefCell<Grammar>>) {

// 	// Rule name.
// 	let rule_name = match parser.token {
// 		Some(Token::Ident(ref x)) => x.clone(),
// 		ref x => panic!("Expected rule name, got {:?} instead", x)
// 	};
// 	parser.next();

// 	let retype = match parser.token {
// 		Some(Token::String(ref n)) => Some(n.clone().into_boxed_str()),
// 		_ => None
// 	};
// 	if retype.is_some() {
// 		parser.next();
// 	}

// 	let rule_cell = {
// 		let mut grammar_mut = grammar.borrow_mut();
// 		let rule = Rc::new(RefCell::new(Rule {
// 			id: grammar_mut.rules.len(),
// 			grammar: Rc::downgrade(grammar),
// 			name: rule_name.into_boxed_str(),
// 			variants: Vec::new(),
// 			retype: retype,
// 		}));
// 		grammar_mut.rules.push(rule.clone());
// 		rule
// 	};
// 	let mut rule = rule_cell.borrow_mut();

// 	match parser.token {
// 		Some(Token::Colon) => parser.next(),
// 		Some(Token::Semicolon) => { parser.next(); return; },
// 		ref x => panic!("In rule '{}': Expected ':' or ';' after rule name, got {:?} instead", rule.name, x)
// 	};

// 	// Variants.
// 	loop {
// 		let mut variant = Variant {
// 			id: rule.variants.len(),
// 			rule: Rc::downgrade(&rule_cell),
// 			symbols: Vec::new(),
// 			reducer: None,
// 		};

// 		loop {
// 			variant.symbols.push(match parser.token {
// 				Some(Token::Ident(ref x)) => RefCell::new(Symbol::Unresolved(x.clone())),
// 				_ => break,
// 			});
// 			parser.next();
// 		}

// 		// Parse the reduction rule name.
// 		match parser.token {
// 			Some(Token::Greater) => {
// 				parser.next();
// 				match parser.token {
// 					Some(Token::Ident(ref x)) => variant.reducer = Some(x.clone().into_boxed_str()),
// 					ref x => panic!("In rule '{}': Expected reducer name after '>', got {:?} instead", rule.name, x)
// 				};
// 				parser.next();
// 			},
// 			_ => (),
// 		}

// 		// Add the variant to the rule.
// 		rule.variants.push(Rc::new(RefCell::new(variant)));

// 		// Decide whether to continue or finish this rule.
// 	    match parser.token {
// 	    	Some(Token::Pipe) => { parser.next(); continue; },
// 	    	Some(Token::Semicolon) => { parser.next(); break; },
// 			ref x => panic!("In rule '{}': Expected terminal, non-terminal, '|', or ';', got {:?} instead", rule.name, x)
// 	    }
// 	}
// }
