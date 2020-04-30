// RUN: moore %s -e split_ports -Vports

module split_ports (a[7:4], a[3:0]);
    // First port is upper 4 bits of 'a'.
    // Second port is lower 4 bits of 'a'.
    // Cannot use named port connections because
    // of part-select port 'a'.
    input [7:0] a;

    // CHECK: Ports of `split_ports`:
    // CHECK:   internal:
    // CHECK:     0: input wire logic [7:0] a
    // CHECK:   external:
    // CHECK:     0: a[..]
    // CHECK:     1: a[..]
endmodule
