// Copyright (c) 2016-2019 Fabian Schuiki

mod common;
use common::*;

/// Compile a module in a piece of verilog code and return the LLHD.
fn compile_module(name: &str, code: &str) -> String {
    simple_logger::init().is_ok();
    let sess = Session::new();
    let ast = parse(code);
    let gcx = GlobalContext::new(&sess);
    let cx = Context::new(&gcx);
    cx.add_root_nodes(&ast).unwrap();
    let m = cx.find_global_item(name.into()).unwrap();
    let code = cx.generate_code(m.into()).unwrap();
    module_to_string(&code)
}

#[test]
fn empty_module() {
    assert_eq!(
        compile_module("foo", "module foo; endmodule").trim(),
        "entity @foo () () {\n}"
    );
}

// #[test]
// fn module_with_trivial_ports() {
//     assert_eq!(
//         compile_module("foo", "module foo (input bit a, output bit z); endmodule").trim(),
//         "entity @foo ($i1 %a) ($i1 %b) {\n}"
//     );
// }
