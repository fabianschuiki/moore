// RUN: moore %s -e renamed_concat -Vports

module renamed_concat (.a({b,c}), f, .g(h[1]));
    // Names 'b', 'c', 'f', 'h' are defined inside the module.
    // Names 'a', 'f', 'g' are defined for port connections.
    // Can use named port connections.

    input b, c, f;
    input [1:0] h;

    // CHECK: Ports of `renamed_concat`:
    // CHECK:   internal:
    // CHECK:     0: input wire logic b
    // CHECK:     1: input wire logic c
    // CHECK:     2: input wire logic f
    // CHECK:     3: input wire logic [1:0] h
    // CHECK:   external:
    // CHECK:     0: .a({b, c})
    // CHECK:     1: .f(f)
    // CHECK:     2: .g(h[..])
endmodule
