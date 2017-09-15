// Copyright (c) 2017 Fabian Schuiki

//! This crate implements VHDL for the moore compiler.

extern crate moore_common;
extern crate rustc_serialize;
extern crate num;

pub mod syntax;
pub mod symtbl;
pub mod pass;
