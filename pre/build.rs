// Copyright (c) 2016 Fabian Schuiki
use std::env;
use std::path::Path;

fn main() {
	let out_dir = env::var("OUT_DIR").unwrap();
	let dst_path = Path::new(&out_dir);
	println!("build.rs into {}", dst_path.to_str().unwrap());
}
