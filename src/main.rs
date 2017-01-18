// Copyright (c) 2016-2017 Fabian Schuiki
extern crate owning_ref;
extern crate clap;
pub mod lexer;
pub mod svlog;
pub mod vhdl;
pub mod errors;
pub mod name;
pub mod source;
use clap::{Arg, App};
use std::path::Path;


#[derive(Debug)]
enum Language {
	Verilog,
	SystemVerilog,
	Vhdl,
}


fn main() {
	let matches = App::new("moore")
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
			.index(1))
		.get_matches();

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
		Some(ext) => panic!("Unrecognized extension of file {}", filename),
		None => panic!("Unabel to determine language of file {}", filename),
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
				svlog::parser::parse(lexer);
				// for (token, sp) in lexer.map(|x| x.unwrap()) {
				// 	println!("{} [{:?}, {:?}]", sp.extract(), token, sp);
				// }
			}
		}
		x => panic!("{}: Language {:?} not yet supported", filename, x),
	}
}
