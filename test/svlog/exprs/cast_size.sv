// RUN: moore %s -e foo -Vtypes

module foo (input int a, output int b, output int c, output int d);
    localparam int W = 42;
    assign b = W'(a);
    assign c = 42'(a);
    assign d = (42+W)'(a);

    // CHECK: 5: self_type(b) = int
    // CHECK: 5: self_type(W'(a)) = bit signed [41:0]
    // CHECK: 5: self_type(a) = int

    // CHECK: 6: self_type(c) = int
    // CHECK: 6: self_type(42'(a)) = bit signed [41:0]
    // CHECK: 6: self_type(a) = int

    // CHECK: 7: self_type(d) = int
    // CHECK: 7: self_type(42+W)'(a)) = bit signed [83:0]
    // CHECK: 7: self_type(a) = int
endmodule
