// Copyright (c) 2016 Fabian Schuiki
use std::env;
pub mod svlog;

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
		let lexer = svlog::lexer::make(filename);
		for token in lexer {
			println!("  Token {:?}", token);
		}
		println!("  Arrived at end of file");
	}
}
