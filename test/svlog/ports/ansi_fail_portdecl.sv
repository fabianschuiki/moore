// RUN: moore %s -e foo
// FAIL
module foo(input a);
    input a;
    // CHECK: error: port declaration in body of ANSI-style module
endmodule
