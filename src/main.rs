// Copyright (c) 2016-2017 Fabian Schuiki
extern crate owning_ref;
extern crate clap;
extern crate sha1;
extern crate bincode;
extern crate rustc_serialize;
pub mod lexer;
pub mod svlog;
pub mod vhdl;
pub mod errors;
pub mod name;
pub mod source;
use clap::{Arg, App, SubCommand, ArgMatches};
use std::path::Path;


#[derive(Debug)]
enum Language {
	Verilog,
	SystemVerilog,
	Vhdl,
}


pub struct Session {
	pub opts: SessionOptions,
}


#[derive(Debug)]
pub struct SessionOptions {
	pub ignore_duplicate_defs: bool,
}


fn main() {
	let matches = App::new("moore")
		.subcommand(SubCommand::with_name("compile")
			.arg(Arg::with_name("inc")
				.short("I")
				.value_name("DIR")
				.help("Adds a search path for SystemVerilog includes")
				.multiple(true)
				.takes_value(true)
				.number_of_values(1))
			.arg(Arg::with_name("preproc")
				.short("E")
				.help("Only preprocess input files"))
			.arg(Arg::with_name("INPUT")
				.help("The input file to use")
				.required(true)
				.index(1)))
		.subcommand(SubCommand::with_name("elaborate")
			.arg(Arg::with_name("NAME")
				.help("Entity or module to elaborate")
				.required(true)
				.index(1))
			.arg(Arg::with_name("ignore_duplicate_defs")
				.long("ignore-duplicate-defs")
				.help("Ignore multiple module/entity definitions")))
		.get_matches();

	let mut session = Session {
		opts: SessionOptions {
			ignore_duplicate_defs: false,
		}
	};

	if let Some(m) = matches.subcommand_matches("compile") {
		compile(m);
	} else if let Some(m) = matches.subcommand_matches("elaborate") {
		session.opts.ignore_duplicate_defs = m.is_present("ignore_duplicate_defs");
		elaborate(m, &session);
	}
}


fn compile(matches: &ArgMatches) {
	// Prepare a list of include paths.
	let include_paths: Vec<_> = match matches.values_of("inc") {
		Some(args) => args.map(|x| std::path::Path::new(x)).collect(),
		None => Vec::new()
	};
	let filename = matches.value_of("INPUT").unwrap();

	// Detect the file type.
	let language = match Path::new(&filename).extension().and_then(|s| s.to_str()) {
		Some("sv") | Some("svh") => Language::SystemVerilog,
		Some("v") => Language::Verilog,
		Some("vhd") | Some("vhdl") => Language::Vhdl,
		Some(_) => panic!("Unrecognized extension of file '{}'", filename),
		None => panic!("Unable to determine language of file '{}'", filename),
	};

	let sm = source::get_source_manager();
	let source = match sm.open(&filename) {
		Some(s) => s,
		None => panic!("Unable to open input file '{}'", filename),
	};

	match language {
		Language::SystemVerilog | Language::Verilog => {
			// Run the input file only through the SystemVerilog preprocessor if
			// so requested on the command line.
			let preproc = svlog::preproc::Preprocessor::new(source, &include_paths);
			if matches.is_present("preproc") {
				for res in preproc {
					print!("{}", res.unwrap().1.extract());
				}
			} else {
				let lexer = svlog::lexer::Lexer::new(preproc);
				let ast = match svlog::parser::parse(lexer) {
					Ok(x) => x,
					Err(()) => std::process::exit(1),
				};

				// TODO: Serialize the parsed AST to disk. If a file is parsed
				// multiple times, the tree of the previous iteration needs to
				// be removed. Upon elaboration, it must be possible to
				// efficiently query the AST for identifiers and check in which
				// subtree the node lives.

				let key = {
					let mut s = sha1::Sha1::new();
					s.update(filename.as_bytes());
					s.digest().to_string()
				};
				svlog::store::store_items(".moore", &key, ast).unwrap();
			}
		}
		x => panic!("{}: Language {:?} not yet supported", filename, x),
	}
}


fn elaborate(matches: &ArgMatches, session: &Session) {
	// Load the syntax trees previously parsed and stored into the library.
	let ast = svlog::store::load_items(".moore").unwrap();

	// TODO: Renumber the AST.

	// Build a symbol table from the loaded syntax trees.
	let symtbl = svlog::resolve::build_symtbl(&ast, session);
}
