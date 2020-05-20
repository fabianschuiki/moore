// RUN: moore %s -e A -e C -e N1 -e N2 -e N3

module X (input int a, output int b);
endmodule

module A;
    int a, b;
    X foo(a, b);
endmodule

// CHECK: entity @A () -> () {
// CHECK:     %0 = const i32 0
// CHECK:     %a = sig i32 %0
// CHECK:     %b = sig i32 %0
// CHECK:     %a1 = prb i32$ %a
// CHECK:     %1 = sig i32 %0
// CHECK:     %2 = const time 0s 1e
// CHECK:     drv i32$ %1, %a1, %2
// CHECK:     inst @X.param1 (i32$ %1) -> (i32$ %b)
// CHECK: }

// module B1 ({x,y});
//     input x;
//     input y;
// endmodule

// module B0;
//     logic [1:0] x;
//     B1 foo(x);
// endmodule


module C;
    int a, b;
    X foo(a + 2, b);
endmodule

// CHECK: entity @C () -> () {
// CHECK:     %0 = const i32 0
// CHECK:     %a = sig i32 %0
// CHECK:     %b = sig i32 %0
// CHECK:     %a1 = prb i32$ %a
// CHECK:     %1 = const i32 2
// CHECK:     %2 = add i32 %a1, %1
// CHECK:     %3 = sig i32 %0
// CHECK:     %4 = const time 0s 1e
// CHECK:     drv i32$ %3, %2, %4
// CHECK:     inst @X.param1 (i32$ %3) -> (i32$ %b)
// CHECK: }

module N1;
    int a, b;
    X foo(.a, .b);
endmodule

module N2;
    int a, b;
    X foo(.*);
endmodule

module N3;
    int a, b;
    X foo(a, .b());
endmodule
