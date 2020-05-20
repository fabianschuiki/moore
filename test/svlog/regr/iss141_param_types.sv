// RUN: moore %s -e foo -O0 -Vtypes

module foo;
    localparam bit [7:0] X = 42'd123;
    bit [9:0] x = X;
    // CHECK: %0 = const i10 123
    // CHECK: %x = sig i10 %0
endmodule
