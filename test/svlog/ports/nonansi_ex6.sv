// RUN: moore %s -e same_input -Vports

module same_input (a,a);
    input a; // This is legal. The inputs are tied together.

    // CHECK: internal:
    // CHECK: 0: input wire logic a
    // CHECK: external:
    // CHECK: 0: .a(a)
    // CHECK: 1: .a(a)
endmodule
