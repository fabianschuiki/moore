// RUN: moore %s -e foo
// FAIL
module foo(input a, input a);
    // CHECK: error: port `a` declared multiple times
endmodule
