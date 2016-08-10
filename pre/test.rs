// Copyright (c) 2016 Fabian Schuiki
use std::path::Path;
mod pargen;


fn main() {
	pargen::generate(Path::new("../src/vhdl/grammar"), Path::new("/tmp/vhdl-parser.rs"));
}
