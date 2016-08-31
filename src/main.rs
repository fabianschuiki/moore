// Copyright (c) 2016 Fabian Schuiki
use std::env;
pub mod lexer;
pub mod svlog;
pub mod vhdl;
pub mod errors;

/// Print a line to standard error.
macro_rules! stderrln {
	($($arg:tt)*) => ({
		use std::io::Write;
		match writeln!(&mut std::io::stderr(), $($arg)*) {
			Ok(_) => {},
			Err(x) => panic!("Unable to write to stderr (file handle closed?): {}", x),
		}
	})
}

fn main() {
	let args: Vec<String> = env::args().collect();
	if args.len() < 2 {
		stderrln!("usage: {} FILE [FILE ...]", args[0]);
		std::process::exit(1)
	}

	// Process each file passed on the command line.
	for filename in &args[1..] {
		println!("Processing file {}", filename);
		let lexer = vhdl::lexer::make(filename);

		// loop {
		// 	match lexer.next_token() {
		// 		Ok(next) => {
		// 			println!("token: {:?}", next.tkn);
		// 			if next.tkn == vhdl::token::Eof {
		// 				break;
		// 			}
		// 		},
		// 		Err(err) => {
		// 			use std::io::Write;
		// 			writeln!(&mut std::io::stderr(), "error: {}", err.message).unwrap();
		// 			std::process::exit(1)
		// 		},
		// 	}
		// }

		let mut parser = vhdl::parser::Parser::new(Box::new(lexer));
		match parser.parse_design_file() {
			Ok(_) => {
				println!("parsed design file");
			},
			Err(err) => {
				use std::io::Write;
				writeln!(&mut std::io::stderr(), "error: {}", err.message).unwrap();
				std::process::exit(1)
			},
		}
		// loop {
		// 	parser.next();
		// }
	}
}
