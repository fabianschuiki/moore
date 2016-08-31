// Copyright (c) 2016 Fabian Schuiki
#![allow(dead_code,unused_imports)]
use std;
use vhdl::lexer::{Token,Keyword,Symbol};
use vhdl::ast::*;

enum TokenId {
	ARCHITECTURE,
	ENTITY,
	LIBRARY,
	USE,
	IDENT,
	BEGIN,
	END,
	PERIOD,
	SEMICOLON,
	COMMA,
	LPAREN,
	RPAREN,
	IS,
	OF,
	SUFFIX,
	GENERIC,
	PORT,
}

// #[derive(Debug)]
// enum Reduction {
// 	None,
// 	LibraryNameList(Vec<String>),
// }

#[derive(Debug)]
enum Item {
	End,
	Shifted(Token),
	Reduced(RuleId, Reduction),
}

enum Action {
	Shift(StateFn),
	Goto(StateFn),
	Reduce(RuleId, u32, ReduceFn),
}

type StateFn = fn(&Item) -> Action;
type ReduceFn = fn(Vec<Item>) -> Reduction;


pub struct Parser<'a> {
	lexer: &'a mut Iterator<Item = Token>,
	item_stack: Vec<Item>,
	lookahead: usize,
	state_stack: Vec<StateFn>,
}


fn next_item(lexer: &mut Iterator<Item = Token>) -> Item {
	loop {
		match lexer.next() {
			Some(Token::Comment(_)) => (),
			Some(tkn) => return Item::Shifted(tkn),
			None => return Item::End,
		}
	}
}


impl<'a> Parser<'a> {
	pub fn new(lexer: &'a mut Iterator<Item = Token>) -> Parser {
		let next = next_item(lexer);
		Parser {
			lexer: lexer,
			item_stack: vec![next],
			lookahead: 0,
			state_stack: vec![action_0],
		}
	}

	pub fn next(&mut self) {
		let action = (self.state_stack[self.state_stack.len()-1])(&self.item_stack[self.lookahead]);
		match action {
			Action::Shift(tr) => {
				// println!("shift {:?}", &self.item_stack[self.lookahead]);
				let next = next_item(self.lexer);
				self.item_stack.push(next);
				self.lookahead += 1;
				self.state_stack.push(tr);
				// println!("item_stack: {:?}", self.item_stack);
				// println!("state_stack: {} states", self.state_stack.len());
			},
			Action::Goto(tr) => {
				// println!("goto with {:?}", &self.item_stack[self.lookahead]);
				// println!("item_stack: {:?}", self.item_stack);
				self.state_stack.push(tr);
				self.lookahead += 1;
			},
			Action::Reduce(id, num, reducefn) => {
				// println!("reduce {:?} covering {} items", id, num);
				// println!("item_stack: {:?}", self.item_stack);
				let lookahead = self.item_stack.pop().unwrap();
				let items = {
					let new_len = self.item_stack.len() - num as usize;
					self.item_stack.split_off(new_len)
				};
				let new_len = self.state_stack.len() - num as usize;
				self.state_stack.truncate(new_len);
				self.item_stack.push(Item::Reduced(id, reducefn(items)));
				self.item_stack.push(lookahead);
				self.lookahead -= num as usize;
				// println!("item_stack: {:?}", self.item_stack);
				// println!("state_stack: {} states", self.state_stack.len());
			}
		}
		assert!(self.lookahead < self.state_stack.len());
	}
}


fn reduce_library_clause(_: Token, names: Vec<String>, _: Token) -> Reduction {
	println!("Found a library clause {:?}", names);
	// Reduction::Debug("a library clause".to_owned())
	Reduction::None
}

fn reduce_library_name_list_x(x: Token) -> Vec<String> {
	match x {
		Token::Ident(name) => vec![name],
		_ => panic!("invalid token"),
	}
}

fn reduce_library_name_list_xs(mut ls: Vec<String>, _: Token, x: Token) -> Vec<String> {
	match x {
		Token::Ident(name) => {
			ls.push(name);
			ls
		},
		_ => panic!("invalid token"),
	}
}


fn start_entity(_: Token, name: Token, _:Token) -> Box<Entity> {
	match name {
		Token::Ident(ref name) => Box::new(Entity::new(name)),
		_ => panic!("Entity name token should by ident")
	}
}

fn add_entity_generic(entity: Box<Entity>, _: Token, _: Token, intfs: Vec<Box<IntfDecl>>, _: Token) -> Box<Entity> {
	println!("Add generic to entity {}: {:?}", entity.get_name(), intfs);
	entity
}

fn add_entity_port(entity: Box<Entity>, _: Token, _: Token, intfs: Vec<Box<IntfDecl>>, _: Token) -> Box<Entity> {
	println!("Add port to entity {}: {:?}", entity.get_name(), intfs);
	entity
}

fn reduce_intf_signal_decl(names: Vec<String>, _: Token, mode: Mode, st: SubtypeIndication) -> Box<IntfDecl> {
	println!("Found signal {:?} intf decl {:?} {:?}", names, mode, st);
	Box::new(IntfDecl::None)
}


fn start_ident_list(x: Token) -> Vec<String> {
	match x {
		Token::Ident(name) => vec![name],
		_ => panic!("ident list needs an ident token")
	}
}

fn extend_ident_list(mut ls: Vec<String>, _: Token, x: Token) -> Vec<String> {
	match x {
		Token::Ident(name) => {
			ls.push(name);
			ls
		},
		_ => panic!("ident list needs an ident token")
	}
}

fn reduce_mode(x: Token) -> Mode {
	match x {
		Token::Keyword(Keyword::In) => Mode::In,
		Token::Keyword(Keyword::Out) => Mode::Out,
		Token::Keyword(Keyword::Inout) => Mode::Inout,
		Token::Keyword(Keyword::Buffer) => Mode::Buffer,
		Token::Keyword(Keyword::Linkage) => Mode::Linkage,
		_ => panic!("invalid mode keyword")
	}
}

fn start_subtype_indication(name: Name) -> SubtypeIndication {
	SubtypeIndication::new(name)
}


fn reduce_simple_name(ident: Token) -> Name {
	match ident {
		Token::Ident(name) => Name::Simple(name.into_boxed_str()),
		_ => panic!("simple_name requires identifier")
	}
}

fn reduce_selected_name(x: Name, _: Token, y: Token) -> Name {
	match y {
		Token::Ident(name) => Name::SelectOne(Box::new(x), name.into_boxed_str()),
		Token::Keyword(Keyword::All) => Name::SelectAll(Box::new(x)),
		_ => panic!("selected_name requires identifier or all keyword")
	}
}


// Include the automatically generated part of the parser.
include!(concat!(env!("OUT_DIR"), "/vhdl-parser.rs"));
