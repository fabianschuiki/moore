// RUN: moore %s -e foo -Vports

module foo (
    bar x
    // bar.ber y
);
    // CHECK: Ports of `foo`:
    // CHECK:   internal:
    // CHECK:     0: inout wire bar x
    // CHECK:   external:
    // CHECK:     0: .x(x)
endmodule

interface bar;
    logic a;
    // modport ber (input a, output b);
endinterface
