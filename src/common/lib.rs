// Copyright (c) 2017 Fabian Schuiki

//! This crate contains the fundamental utilities used to by the rest of the
//! moore compiler.

extern crate rustc_serialize;
extern crate memmap;
#[macro_use]
extern crate bitflags;

pub mod errors;
pub mod lexer;
pub mod name;
pub mod source;
pub mod grind;
pub mod id;
pub mod score;
pub mod util;

pub use self::id::NodeId;
use errors::{DiagBuilder2, DiagEmitter, Severity};
use std::cell::Cell;

pub struct Session {
	pub opts: SessionOptions,
	/// Whether any error diagnostics were produced.
	pub failed: Cell<bool>,
}

impl Session {
	/// Create a new session.
	pub fn new() -> Session {
		Session {
			opts: Default::default(),
			failed: Cell::new(false),
		}
	}
}

impl DiagEmitter for Session {
	fn emit(&self, diag: DiagBuilder2) {
		if diag.severity >= Severity::Error {
			self.failed.set(true);
		}
		eprintln!("{}", diag);
	}
}

/// A set of options for a session.
///
/// The arguments passed on the command line are intended to modify these values
/// in order to configure the execution of the program.
#[derive(Debug, Default)]
pub struct SessionOptions {
	pub ignore_duplicate_defs: bool,
	/// Print a trace of scoreboard invocations for debugging purposes.
	pub trace_scoreboard: bool,
	/// The verbosity options.
	pub verbosity: Verbosity,
}

bitflags! {
	/// A set of verbosity options for a session.
	///
	/// These flags control how much information the compiler emits.
	#[derive(Default)]
	pub struct Verbosity: u8 {
		const TYPES         = 0b00001;
		const EXPR_TYPES    = 0b00010;
		const TYPE_CONTEXTS = 0b00100;
		const TYPECK        = 0b01000;
		const NAMES         = 0b10000;
	}
}
