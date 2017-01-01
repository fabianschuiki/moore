// Copyright (c) 2016-2017 Fabian Schuiki
use std::env;
use std::path::Path;
mod pargen;


fn main() {
	let out_dir = env::var("OUT_DIR").unwrap();
	let dst_path = Path::new(&out_dir);

	// pargen::generate(Path::new("src/svlog/grammar"), &dst_path.join("svlog-parser.rs"));
	// pargen::generate(Path::new("src/vhdl/grammar"), &dst_path.join("vhdl-parser.rs"));
}
