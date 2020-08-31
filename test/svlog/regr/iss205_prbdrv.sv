// RUN: moore %s -e A

module A(input clk);
    B b0(clk);
    B b1(clk ^ 1'b1);
endmodule

module B(input clk);
endmodule

// CHECK: entity @B.param1 (i1$ %clk) -> () {
// CHECK: }

// CHECK: entity @A (i1$ %clk) -> () {
// CHECK:     inst @B.param1 (i1$ %clk) -> ()
// CHECK:     %clk.prb = prb i1$ %clk
// CHECK:     %0 = not i1 %clk.prb
// CHECK:     %1 = const i1 0
// CHECK:     %2 = sig i1 %1
// CHECK:     %3 = const time 0s 1d
// CHECK:     drv i1$ %2, %0, %3
// CHECK:     inst @B.param1 (i1$ %2) -> ()
// CHECK: }
