// RUN: moore %s -e foo
// IGNORE

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
endmodule
