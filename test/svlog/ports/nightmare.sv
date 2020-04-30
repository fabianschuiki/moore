// RUN: moore %s -e foo -Vports

module foo (
    .P1(x1[3:0]),
    .P2(x1[7:0]),
    .P3(x2),
    P4,
    .P5({x3, x4}),
    {x5, x6},
    .P6()
);
    // This language needs to die.
    output [7:0] x1;
    ref x2;
    input P4;
    input x3, x5;
    output x4, x6;

    logic [7:0] x1;
    int x2;

    // CHECK: Ports of `foo`:
    // CHECK:   internal:
    // CHECK:     0: output var logic [7:0] x1
    // CHECK:     1: ref var int x2
    // CHECK:     2: input wire logic P4
    // CHECK:     3: input wire logic x3
    // CHECK:     4: input wire logic x5
    // CHECK:     5: output wire logic x4
    // CHECK:     6: output wire logic x6
    // CHECK:   external:
    // CHECK:     0: .P1(x1[..])
    // CHECK:     1: .P2(x1[..])
    // CHECK:     2: .P3(x2)
    // CHECK:     3: .P4(P4)
    // CHECK:     4: .P5({x3, x4})
    // CHECK:     5: {x5, x6}
    // CHECK:     6: .P6()

    // CHECK: entity @foo (i32$ %x2, i1$ %P4, i1$ %x3, i1$ %x5) -> (i8$ %x1, i1$ %x4, i1$ %x6) {
endmodule
