// Copyright (c) 2017 Fabian Schuiki
#![allow(dead_code)]
#![allow(unused_variables)]

//! A VHDL parser.

pub mod token_stream;
#[macro_use]
mod core;
pub mod rules;
pub mod basic;

#[cfg(test)]
mod test;

pub use self::token_stream::TokenStream;
