// Copyright (c) 2016-2020 Fabian Schuiki

use moore_common::source::get_source_manager;
use moore_svlog_syntax::{lexer::Lexer, parser, preproc::Preprocessor};

pub(crate) use moore_svlog_syntax::ast;

pub(crate) fn parse(input: &str) -> ast::Root {
    use std::cell::Cell;
    thread_local!(static INDEX: Cell<usize> = Cell::new(0));
    let sm = get_source_manager();
    let idx = INDEX.with(|i| {
        let v = i.get();
        i.set(v + 1);
        v
    });
    let source = sm.add(&format!("test_{}.sv", idx), input);
    let pp = Preprocessor::new(source, &[], &[]);
    let lexer = Lexer::new(pp);
    parser::parse(lexer).unwrap()
}
