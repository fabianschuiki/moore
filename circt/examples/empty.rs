use circt::*;

fn main() {
    let cx = mlir::Context::new();
    cx.load_dialect(hw::dialect());
    cx.load_dialect(comb::dialect());
    cx.load_dialect(seq::dialect());
}
