// RUN: moore %s -e foo -Vports

module foo(a, b);
    input a;
    bit a;
    // CHECK: 0: input var bit a

    input b;
    wire bit b;
    // CHECK: 1: input wire bit b
endmodule
