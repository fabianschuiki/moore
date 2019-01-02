// Copyright (c) 2016-2017 Fabian Schuiki

//! A hardware description language compiler.

#![allow(dead_code)]
#![allow(unused_variables)]

extern crate bincode;
extern crate rustc_serialize;
extern crate typed_arena;
extern crate llhd;

// Re-export everything from the common crate.
#[macro_use]
pub extern crate moore_common as common;
pub use crate::common::*;

// Pull in subcrates. We might want to feature-gate this at some point.
pub extern crate moore_svlog as svlog;
pub extern crate moore_vhdl as vhdl;

pub mod score;
