// RUN: moore %s -e mixed_direction -Vports

module mixed_direction (.p({a, e}));
    input a; // p contains both input and output directions.
    output e;

    // CHECK: Ports of `mixed_direction`:
    // CHECK:   internal:
    // CHECK:     0: input wire logic a
    // CHECK:     1: output wire logic e
    // CHECK:   external:
    // CHECK:     0: .p({a, e})

    // CHECK: entity @mixed_direction (i1$ %a) -> (i1$ %e) {
endmodule
