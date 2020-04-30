// Copyright (c) 2016-2020 Fabian Schuiki
#![allow(dead_code)]
#![allow(unused_variables)]

//! A VHDL parser.

pub mod token_stream;
#[macro_use]
mod core;
pub mod basic;
pub mod rules;

#[cfg(test)]
mod test;

pub use self::token_stream::TokenStream;
