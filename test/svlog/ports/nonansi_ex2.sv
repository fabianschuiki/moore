// RUN: moore %s -e complex_ports -Vports

module complex_ports ({c,d}, .e(f));
    // Nets {c,d} receive the first port bits.
    // Name 'f' is declared inside the module.
    // Name 'e' is defined outside the module.
    // Cannot use named port connections of first port.
    input c, d, f;

    // CHECK: Ports of `complex_ports`:
    // CHECK:   internal:
    // CHECK:     0: input wire logic c
    // CHECK:     1: input wire logic d
    // CHECK:     2: input wire logic f
    // CHECK:   external:
    // CHECK:     0: {c, d}
    // CHECK:     1: .e(f)

    // CHECK: entity @complex_ports (i1$ %c, i1$ %d, i1$ %f) -> () {
endmodule
