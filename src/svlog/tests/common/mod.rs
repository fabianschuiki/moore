// Copyright (c) 2016-2020 Fabian Schuiki
#![allow(dead_code)]

//! Utilities for verilog tests.

pub extern crate llhd;
pub extern crate moore_common;
pub extern crate moore_svlog as svlog;
pub extern crate simple_logger;
pub use crate::moore_common::Session;
pub use crate::svlog::*;

pub fn parse(input: &str) -> Vec<ast::Root> {
    use crate::moore_common::source::get_source_manager;
    use std::cell::Cell;
    thread_local!(static INDEX: Cell<usize> = Cell::new(0));
    let sm = get_source_manager();
    let idx = INDEX.with(|i| {
        let v = i.get();
        i.set(v + 1);
        v
    });
    let source = sm.add(&format!("test_{}.sv", idx), input);
    let pp = preproc::Preprocessor::new(source, &[], &[]);
    let lexer = lexer::Lexer::new(pp);
    match parser::parse(lexer) {
        Ok(x) => vec![x],
        Err(_) => panic!("parsing failed"),
    }
}

pub(crate) fn module_to_string(module: &llhd::ir::Module) -> String {
    llhd::assembly::write_module_string(module)
}
