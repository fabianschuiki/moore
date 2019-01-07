// Copyright (c) 2016-2019 Fabian Schuiki

mod common;
use crate::common::*;

/// Compile a module in a piece of verilog code and return the LLHD.
fn compile_module(name: &str, code: &str) -> String {
    simple_logger::init().is_ok();
    let sess = Session::new();
    let store = GlobalArenas::default();
    let ast = parse(code);
    let cx = GlobalContext::new(&sess, &store);
    cx.add_root_nodes(ast.iter());
    let m = cx.find_module(name.into()).unwrap();
    let mut cg = CodeGenerator::new(&cx);
    cg.emit_module(m.into()).unwrap();
    module_to_string(&cg.finalize())
}

#[test]
fn empty_module() {
    assert_eq!(
        compile_module("foo", "module foo; endmodule").trim(),
        "entity @foo () () {\n}"
    );
}

#[test]
fn module_with_trivial_ports() {
    assert_eq!(
        compile_module("foo", "module foo (input bit a, output bit b); endmodule").trim(),
        "entity @foo (i1$ %a) (i1$ %b) {\n    drv %b 0\n}"
    );
}

#[test]
fn empty_instances() {
    assert_eq!(
        compile_module(
            "foo",
            "
            module foo;
                bar b();
            endmodule

            module bar;
            endmodule
            "
        )
        .trim(),
        "entity @bar () () {\n}\n\nentity @foo () () {\n    inst @bar () ()\n}"
    );
}
