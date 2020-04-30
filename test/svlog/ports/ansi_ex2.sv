// RUN: moore %s -e mymod -Vports

module mymod (
    output .P1(r[3:0]),
    output .P2(r[7:4]),
    ref .Y(x),
    input R
);
    logic [7:0] r;
    int x;

    // CHECK: Ports of `mymod`:
    // CHECK:   internal:
    // CHECK:     0: output wire logic [7:0] r
    // CHECK:     1: ref var int x
    // CHECK:     2: input wire logic R
    // CHECK:   external:
    // CHECK:     0: .P1(r[..])
    // CHECK:     1: .P2(r[..])
    // CHECK:     2: .Y(x)
    // CHECK:     3: .R(R)

    // CHECK: entity @mymod (i32$ %x, i1$ %R) -> (i8$ %r) {
endmodule
