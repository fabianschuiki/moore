// IGNORE
// @exclude

module mh0 (wire x);
    // inout wire logic x
endmodule

module mh1 (integer x);
    // inout wire integer x
endmodule

module mh2 (inout integer x);
    // inout wire integer x
endmodule

module mh3 ([5:0] x);
    // inout wire logic [5:0] x
endmodule

module mh5 (input x);
    // input wire logic x
endmodule

module mh6 (input var x);
    // input var logic x
endmodule

module mh7 (input var integer x);
    // input var integer x
endmodule

module mh8 (output x);
    // output wire logic x
endmodule

module mh9 (output var x);
    // output var logic x
endmodule

module mh10(output signed [5:0] x);
    // output wire logic signed [5:0] x
endmodule

module mh11(output integer x);
    // output var integer x
endmodule

module mh12(ref [5:0] x);
    // ref var logic [5:0] x
endmodule

module mh13(ref x [5:0]);
    // ref var logic x [5:0]
endmodule

module mh14(wire x, y[7:0]);
    // inout wire logic x
    // inout wire logic y[7:0]
endmodule

module mh15(integer x, signed [5:0] y);
    // inout wire integer x
    // inout wire logic signed [5:0] y
endmodule

module mh16([5:0] x, wire y);
    // inout wire logic [5:0] x
    // inout wire logic y
endmodule

module mh17(input var integer x, wire y);
    // input var integer x
    // input wire logic y
endmodule

module mh18(output var x, input y);
    // output var logic x
    // input wire logic y
endmodule

module mh19(output signed [5:0] x, integer y);
    // output wire logic signed [5:0] x
    // output var integer y
endmodule

module mh20(ref [5:0] x, y);
    // ref var logic [5:0] x
    // ref var logic [5:0] y
endmodule

module mh21(ref x [5:0], y);
    // ref var logic x [5:0]
    // ref var logic y
endmodule
