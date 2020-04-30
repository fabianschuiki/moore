// RUN: moore %s -e same_port -Vports

module same_port (.a(i), .b(i));
    // Name 'i' is declared inside the module as an inout port.
    // Names 'a' and 'b' are defined for port connections.
    inout i;

    // CHECK: Ports of `same_port`:
    // CHECK:   internal:
    // CHECK:     0: inout wire logic i
    // CHECK:   external:
    // CHECK:     0: .a(i)
    // CHECK:     1: .b(i)
endmodule
