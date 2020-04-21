// RUN: moore %s -e foo
// FAIL
module foo(a, b);
    input wire a;
    input logic b;

    wire a;
    // CHECK: error: port `a` is complete; additional declaration forbidden

    logic b;
    // CHECK: error: port `b` is complete; additional declaration forbidden
endmodule
