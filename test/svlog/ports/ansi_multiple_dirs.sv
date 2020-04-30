// RUN: moore %s -e foo -e bar

module foo (
    input  .a(x),
    output .b(x)
);
    logic x;

    //! CHECK: entity @foo () -> (i1$ %x1) {
endmodule


module bar (
    input  .a(x[0]),
    output .b(x[1])
);
    logic [1:0] x;

    //! CHECK: entity @bar (i1$ %x) -> (i1$ %x1) {
endmodule
