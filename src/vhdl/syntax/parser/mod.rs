// Copyright (c) 2017 Fabian Schuiki
#![allow(dead_code)]
#![allow(unused_variables)]

//! A VHDL parser.

mod token_stream;
pub mod rules;
pub mod basic;
mod core;

#[cfg(test)]
mod test;

pub use self::token_stream::TokenStream;
