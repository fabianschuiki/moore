// RUN: moore %s -e foo
// FAIL
module foo(a[$]);
    // CHECK: error: invalid port range `[$]`; on port `a`
endmodule
