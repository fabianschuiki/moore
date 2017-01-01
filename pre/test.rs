// Copyright (c) 2016-2017 Fabian Schuiki
use std::path::Path;
mod pargen;


fn main() {
	// pargen::generate(Path::new("../src/vhdl/grammar"), Path::new("/tmp/vhdl-parser.rs"));
	pargen::generate(Path::new("../src/svlog/grammar"), Path::new("/tmp/svlog-parser.rs"));
}
