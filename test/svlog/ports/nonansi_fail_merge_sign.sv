// RUN: moore %s -e foo
// FAIL
module foo(a, b);
    input signed a;
    logic unsigned a;
    // CHECK: error: port `a` has contradicting signs

    input signed b;
    wire unsigned b;
    // CHECK: error: port `b` has contradicting signs
endmodule
