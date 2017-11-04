// Copyright (c) 2017 Fabian Schuiki

//! A lexical analyzer and parser for VHDL source files as per
//! IEEE 1076-2008.

extern crate moore_common;
extern crate rustc_serialize;

pub mod lexer;
pub mod parser;
pub mod ast;

use moore_common::grind::{self, Grinder};
use moore_common::source::*;
use moore_common::errors::*;


pub fn parse(src: Source) -> Result<Vec<ast::DesignUnit>,()> {
	use self::parser::token_stream::TokenStream;

	// Get a grinder on the bytes of the source file.
	let content = src.get_content();
	let bytes = grind::from_iter(content.bytes().iter().map(|x| *x))
		.vent(|err: DiagBuilder2| println!("{}", err));

	// Perform lexical analysis on the bytes.
	let tokens = lexer::Lexer::new(bytes, src);

	// Parse the file.
	let mut parser = parser::basic::BasicParser::new(tokens);
	let ast = parser::rules::parse_design_file(&mut parser);

	if parser.is_error() {
		Err(())
	} else {
		Ok(ast)
	}
}
