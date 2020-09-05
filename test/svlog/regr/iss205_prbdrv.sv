// RUN: moore %s -e A -e B -e D -O0

module A(input clk);
    C c0(clk);
    C c1(clk);
endmodule

module B(input clk);
    C c0(clk);
    C c1(clk ^ 1'b1);
endmodule

module C(input clk);
endmodule

// CHECK: entity @C.param1 (i1$ %clk) -> () {
// CHECK: }

// CHECK: entity @A (i1$ %clk) -> () {
// CHECK:     inst @C.param1 (i1$ %clk) -> ()
// CHECK:     inst @C.param1 (i1$ %clk) -> ()
// CHECK: }

// CHECK: entity @B (i1$ %clk) -> () {
// CHECK:     inst @C.param1 (i1$ %clk) -> ()
// CHECK:     %clk.prb = prb i1$ %clk
// CHECK:     %0 = const i1 1
// CHECK:     %1 = xor i1 %clk.prb, %0
// CHECK:     %2 = const i1 0
// CHECK:     %3 = sig i1 %2
// CHECK:     %4 = const time 0s 1d
// CHECK:     drv i1$ %3, %1, %4
// CHECK:     inst @C.param1 (i1$ %3) -> ()
// CHECK: }

interface I;
    logic clk;
    modport in (input clk);
endinterface

module D(I.in i, I.in j[2]);
    E e0(i);
    E e1(j[0]);
    E e2(j[1]); // breaks optimization at the moment
endmodule

module E(I.in i);
endmodule

// CHECK: entity @E.param4 (i1$ %i.clk) -> () {
// CHECK: }

// CHECK: entity @E.param5 (i1$ %i.clk) -> () {
// CHECK: }

// CHECK: entity @E.param6 (i1$ %i.clk) -> () {
// CHECK: }

// CHECK: entity @D (i1$ %i.clk, [2 x i1]$ %j.clk) -> () {
// CHECK:     inst @E.param4 (i1$ %i.clk) -> ()
// CHECK:     %0 = const i32 0
// CHECK:     %4 = shr [2 x i1]$ %j.clk, [2 x i1]$ %3, i32 %0
// CHECK:     %5 = extf i1$, [2 x i1]$ %4, 0
// CHECK:     inst @E.param5 (i1$ %5) -> ()
// CHECK:     %6 = const i32 1
// CHECK:     %10 = shr [2 x i1]$ %j.clk, [2 x i1]$ %9, i32 %6
// CHECK:     %11 = extf i1$, [2 x i1]$ %10, 0
// CHECK:     inst @E.param6 (i1$ %11) -> ()
// CHECK: }
