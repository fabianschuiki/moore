// RUN: moore %s -e foo
// IGNORE  see issue #141

module foo;
    localparam bit [7:0] X = 42'd123;
    bit [9:0] x = X;
    // CHECK: %0 = const i10 123
    // CHECK: %x = sig i10 %0
endmodule
