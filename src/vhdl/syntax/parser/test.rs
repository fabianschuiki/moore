// Copyright (c) 2017 Fabian Schuiki

use std::fmt::Debug;
use moore_common::errors::*;
use moore_common::name::*;
use moore_common::source::*;
use moore_common::grind::{self, Grinder};
use syntax::lexer::Lexer;
use syntax::lexer::token;
use syntax::parser::rules::*;
use syntax::parser::core::*;
use syntax::parser::basic::BasicParser;
use syntax::ast;

macro_rules! parse {
    ($content:expr, $parse_fn:expr) => {{
		// Create an anonymous source file with the given content.
		let src = get_source_manager().add_anonymous($content);

		// Assemble a parser for the source.
		let content = src.get_content();
		let bytes = grind::from_iter(content.bytes().iter().map(|x| *x))
			.vent(|err: DiagBuilder2| println!("{}", err));
		let tokens = Lexer::new(bytes, src);
		let mut parser = BasicParser::new(tokens);

		// Check the result.
		parse_impl(&mut parser, $parse_fn)
    }}
}

fn parse_impl<P,F,R,E>(p: &mut P, mut parse_fn: F) -> R where
	P: Parser,
	F: FnMut(&mut P) -> Result<R,E>,
	E: Debug {

	// Apply the parser.
	let result = parse_fn(p).expect("parser failed");

	// Check whether the entire input has been consumed.
	match p.peek(0) {
		Spanned{ value: token::Eof, .. } => (),
		Spanned{ value, span } => {
			panic!("{}", DiagBuilder2::error("Not entire input consumed").span(span.begin()));
		}
	}

	result
}


#[test]
fn name() {
	let ast = parse!("
		simple
		'x'
		\"add\"
		simple.simple
		simple.'x'
		simple.\"add\"
		simple.all
		simple'attr
		-- simple[ signature goes here ]'attr
		-- simple(1)
		-- simple(1,2)
		-- simple(1 to 2)
		-- simple(2 downto 1)
	", |p| repeat(p, try_name));
}

#[test]
fn library_clause() {
	parse!("library ieee;", parse_context_item);
}

#[test]
fn use_clause() {
	parse!("use ieee;", parse_context_item);
	parse!("use ieee, ieee.std_logic_1164.all;", parse_context_item);
	parse!("use work.'X', work.\"+\";", parse_context_item);
}

#[test]
fn context_ref() {
	parse!("context ctx;", parse_context_item);
	parse!("context ctx, work, stuff;", parse_context_item);
	parse!("context work.'X', work'blah.text;", parse_context_item);
}

#[test]
fn design_unit() {
	// parse!("entity foo is end;", parse_design_unit);
	// parse!("configuration foo is begin end;", parse_design_unit);
	// parse!("package foo is begin end;", parse_design_unit);
	parse!("context foo is end;", parse_design_unit);
}

#[test]
fn context_decl() {
	parse!("context foo is end;", parse_context_decl);
	parse!("context foo is end context;", parse_context_decl);
	parse!("context foo is end context foo;", parse_context_decl);
	// parse!("context foo is end context bar;", parse_context_decl); // check if this emits a warning
	parse!("
		context project_context is
			library project_lib;
			use project_lib.project_defs.all;
			library IP_lib;
			context IP_lib.IP_context;
		end context project_context;
	", parse_context_decl);
}
