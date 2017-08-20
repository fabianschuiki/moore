// Copyright (c) 2017 Fabian Schuiki

//! A lexical analyzer and parser for VHDL source files as per
//! IEEE 1076-2008.

pub mod lexer;
pub mod parser;
pub mod ast;

use moore_common::grind::{self, Grinder};
use moore_common::source::*;
use moore_common::errors::*;


pub fn parse(src: Source) {
	println!("parsing VHDL source {:?}", src);

	// Get a grinder on the bytes of the source file.
	let content = src.get_content();
	let bytes = grind::from_iter(content.bytes().iter().map(|x| *x))
		.vent(|err: DiagBuilder2| println!("{}", err));

	// Perform lexical analysis on the bytes.
	let tokens = lexer::Lexer::new(bytes, src);

	// Parse the file.
	let mut parser = parser::basic::BasicParser::new(tokens);
	parser::rules::parse_design_file(&mut parser);

	// Parse the file.
	// let mut i = 0;
	// loop {
	// 	let c = tokens.next();
	// 	println!("{:?}", c);
	// 	// i += c.span.begin;
	// 	if c.is_end() {
	// 		break;
	// 	}
	// }

	println!("done");
	// println!("done ({})", i);
}
