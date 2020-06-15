// RUN: moore %s -e foo -e bar
// IGNORE  see #189

module foo (
    input  wire [1:0] x,
    output wire [1:0] z
);
    reg [1:0] y;
    assign y = x;
    assign z = y;
endmodule

module bar (
    input  wire x,
    output wire z
);
    reg y;
    assign y = x;
    assign z = y;
endmodule
