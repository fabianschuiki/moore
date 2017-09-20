// Copyright (c) 2017 Fabian Schuiki

//! This crate contains the fundamental utilities used to by the rest of the
//! moore compiler.

extern crate rustc_serialize;
extern crate memmap;

pub mod errors;
pub mod lexer;
pub mod name;
pub mod source;
pub mod grind;
pub mod id;
pub mod score;

pub use self::id::NodeId;


pub struct Session {
	pub opts: SessionOptions,
}

impl Session {
	pub fn new() -> Session {
		Session {
			opts: SessionOptions {
				ignore_duplicate_defs: false,
				trace_scoreboard: false,
			}
		}
	}
}

#[derive(Debug)]
pub struct SessionOptions {
	pub ignore_duplicate_defs: bool,
	/// Print a trace of scoreboard invocations for debugging purposes.
	pub trace_scoreboard: bool,
}
