// Copyright (c) 2016-2019 Fabian Schuiki

extern crate llhd;
mod common;
use common::*;
use moore_common::Session;
use moore_svlog::{Context, GlobalContext};

#[test]
fn empty_module() {
    let sess = Session::new();
    let ast = parse("module foo; endmodule");
    let gcx = GlobalContext::new(&sess);
    let cx = Context::new(&gcx);
    cx.add_root_nodes(&ast).unwrap();
    let m = cx.find_global_item("foo".into()).unwrap();
    let code = cx.generate_code(m.into()).unwrap();
    let asm = module_to_string(&code);
    eprintln!("{}", asm.trim());
    // assert_eq!(asm.trim(), "entity @foo () () {\n}");
}
