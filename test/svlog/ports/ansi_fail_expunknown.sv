// RUN: moore %s -e foo
// FAIL
module foo (
    input .a(x)
);
    // CHECK: error: `x` not found in module `foo`
endmodule
