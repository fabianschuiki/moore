// RUN: moore %s -e foo

module foo (input [31:0] a);
    // CHECK: entity @foo (i32$ %a) -> () {
    // CHECK: }
endmodule
