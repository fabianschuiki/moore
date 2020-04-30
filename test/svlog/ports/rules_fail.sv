// RUN: moore %s -e mh4
// FAIL

module mh4 (var x);
    // CHECK: error: inout port `x` must be a net; but is declared as variable
endmodule
