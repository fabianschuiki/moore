// Copyright (c) 2017 Fabian Schuiki

//! This crate implements parsing SystemVerilog source files into an abstract
//! syntax tree and resolving the encountered names.

extern crate moore_common;
extern crate rustc_serialize;
extern crate bincode;

pub mod ast;
pub mod cat;
pub mod lexer;
pub mod parser;
pub mod preproc;
pub mod store;
pub mod token;
pub mod resolve;
pub mod renumber;
