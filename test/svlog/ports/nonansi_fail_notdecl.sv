// RUN: moore %s -e foo
// FAIL
module foo(a);
    // CHECK: error: port `a` not declared in module body
endmodule
