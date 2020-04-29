// RUN: moore %s -e A0

module A1 (input int a, output int b);
endmodule

module A0;
    int a, b;
    A1 foo(a, b);
endmodule

// CHECK: entity @A1 (i32$ %a) -> (i32$ %b) {
// CHECK:     %0 = const i32 0
// CHECK:     %1 = const time 0s
// CHECK:     drv i32$ %b, %0, %1
// CHECK: }
// CHECK:
// CHECK: entity @A0 () -> () {
// CHECK:     %0 = const i32 0
// CHECK:     %a = sig i32 %0
// CHECK:     %1 = const i32 0
// CHECK:     %b = sig i32 %1
// CHECK:     %a1 = prb i32$ %a
// CHECK:     %2 = const i32 0
// CHECK:     %3 = sig i32 %2
// CHECK:     %4 = const time 0s 1e
// CHECK:     drv i32$ %3, %a1, %4
// CHECK:     inst @A1 (i32$ %3) -> (i32$ %b)
// CHECK: }

// module B1 ({x,y});
//     input x;
//     input y;
// endmodule

// module B0;
//     logic [1:0] x;
//     B1 foo(x);
// endmodule
