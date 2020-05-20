// RUN: moore %s -e foo -Vtypes

module foo;
    bit [19:0] x;

    bar1 i1 (x);
    bar2 #(7) i2 (x);
    bar3 #(7) i3 (x);
    bar4 #(7, 10) i4 (x);
    bar5 #(7, 10) i5 (x,x);
    bar6 #(bit [16:0]) i6 (x);
    bar7 #(bit [16:0], 10) i7 (x);
    bar8 #(bit [16:0], 10) i8 (x,x);
endmodule

// Simple input type.
module bar1 (
    input bit [6:0] x
);
endmodule

// Simple parameter.
module bar2 #(
    parameter bit [9:0] N
)(
    input bit [6:0] x
);
endmodule

// Value parameter affects port.
module bar3 #(
    parameter bit [9:0] N
)(
    input bit [N-1:0] x
);
endmodule

// Value parameter affects other parameter.
module bar4 #(
    parameter bit [9:0] N,
    parameter bit [N-1:0] M
)(
    input bit [6:0] x
);
endmodule

// Value parameter affects other parameter and port.
module bar5 #(
    parameter bit [9:0] N,
    parameter bit [N-1:0] M
)(
    input bit [N-1:0] x,
    input bit [M-1:0] y
);
endmodule

// Type parameter affects port.
module bar6 #(
    parameter type T
)(
    input T x
);
endmodule

// Type parameter affects other parameter.
module bar7 #(
    parameter type T,
    parameter T N
)(
    input bit [6:0] x
);
endmodule

// Type parameter affects other parameter and port.
module bar8 #(
    parameter type T,
    parameter T N
)(
    input T x,
    input bit [N-1:0] y
);
endmodule
