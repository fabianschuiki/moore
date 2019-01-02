// Copyright (c) 2017 Fabian Schuiki
#![allow(dead_code)]

//! Utilities for verilog tests.

pub extern crate llhd;
pub extern crate moore_common;
pub extern crate moore_svlog;

use self::moore_common::source::get_source_manager;
use self::moore_common::Session;
use self::moore_svlog::*;

pub fn parse(input: &str) -> Vec<ast::Root> {
    use std::cell::Cell;
    thread_local!(static INDEX: Cell<usize> = Cell::new(0));
    let sm = get_source_manager();
    let idx = INDEX.with(|i| {
        let v = i.get();
        i.set(v + 1);
        v
    });
    let source = sm.add(&format!("test_{}.sv", idx), input);
    let pp = preproc::Preprocessor::new(source, &[]);
    let lexer = lexer::Lexer::new(pp);
    match parser::parse(lexer) {
        Ok(x) => vec![x],
        Err(_) => panic!("parsing failed"),
    }
}

pub fn compile_to_hir(mut asts: Vec<ast::Root>) -> hir::Root {
    let session = Session::new();
    renumber::renumber(&mut asts);
    let nameres = resolve::resolve(&session, &asts).expect("name resolution failed");
    let top = (|| {
        for ast in &asts {
            for item in &ast.items {
                if let ast::Item::Module(ref decl) = *item {
                    return decl.id;
                }
            }
        }
        panic!("no module found");
    })();
    hir::lower(&session, &nameres, top, asts).expect("lowering to hir failed")
}

pub(crate) fn unwrap_single_module(hir: &hir::Root) -> &hir::Module {
    assert_eq!(hir.mods.len(), 1);
    hir.mods.iter().nth(0).unwrap().1
}

pub(crate) fn module_to_string(module: &llhd::Module) -> String {
    use llhd::{assembly::writer::Writer, visit::Visitor};
    let mut out = Vec::<u8>::new();
    Writer::new(&mut out).visit_module(&module);
    String::from_utf8(out).unwrap()
}
