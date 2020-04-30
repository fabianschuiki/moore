// Copyright (c) 2016-2020 Fabian Schuiki

//! This crate implements parsing SystemVerilog source files into an abstract
//! syntax tree and resolving the encountered names.

#[macro_use]
extern crate log;

pub mod ast;
pub mod cat;
pub mod lexer;
pub mod parser;
pub mod preproc;
pub mod token;
