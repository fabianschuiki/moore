// Copyright (c) 2017 Fabian Schuiki

//! This crate contains the fundamental utilities used to by the rest of the
//! moore compiler.

extern crate rustc_serialize;
extern crate memmap;

pub mod errors;
pub mod lexer;
pub mod name;
pub mod source;


pub struct Session {
	pub opts: SessionOptions,
}

#[derive(Debug)]
pub struct SessionOptions {
	pub ignore_duplicate_defs: bool,
}
