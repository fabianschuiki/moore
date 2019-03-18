// Copyright (c) 2016-2019 Fabian Schuiki
mod common;
use crate::common::*;

#[test]
fn inside_expr() {
    parse("module A; initial assert(42 inside {-1,0,1}); endmodule");
}
