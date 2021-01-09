// Copyright (c) 2016-2021 Fabian Schuiki

//! A hardware description language compiler.

#![allow(dead_code)]
#![allow(unused_variables)]

#[macro_use]
extern crate log;
#[macro_use]
pub extern crate moore_common as _;

pub use moore_common as common;
pub use moore_common::*;
pub use moore_svlog as svlog;
pub use moore_vhdl as vhdl;

pub mod score;
