use circt::{prelude::*, *};

fn main() {
    let cx = mlir::OwnedContext::new();
    cx.load_dialect(std::dialect());
    cx.load_dialect(hw::dialect());
    cx.load_dialect(comb::dialect());
    cx.load_dialect(llhd::dialect());
    cx.load_dialect(seq::dialect());

    let module = std::ModuleOp::new(*cx);
    module.dump();
}
