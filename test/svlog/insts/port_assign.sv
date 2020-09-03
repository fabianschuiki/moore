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
// CHECK:     inst @X.param1 (i32$ %a) -> (i32$ %b)
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
// CHECK:     %a.prb = prb i32$ %a
// CHECK:     %1 = const i32 2
// CHECK:     %2 = add i32 %a.prb, %1
// CHECK:     %3 = sig i32 %0
// CHECK:     %4 = const time 0s 1d
// CHECK:     drv i32$ %3, %2, %4
// CHECK:     inst @X.param1 (i32$ %3) -> (i32$ %b)
// CHECK: }

module N1;
    int a = 42, b = 42;
    X foo(.a, .b);
endmodule

// CHECK: entity @N1 () -> () {
// CHECK:     %0 = const i32 42
// CHECK:     %a = sig i32 %0
// CHECK:     %b = sig i32 %0
// CHECK:     inst @X.param1 (i32$ %a) -> (i32$ %b)
// CHECK: }

module N2;
    int a = 42, b = 42;
    X foo(.*);
endmodule

// CHECK: entity @N2 () -> () {
// CHECK:     %0 = const i32 42
// CHECK:     %a = sig i32 %0
// CHECK:     %b = sig i32 %0
// CHECK:     inst @X.param1 (i32$ %a) -> (i32$ %b)
// CHECK: }

module N3;
    int a = 42, b = 42;
    X foo(a, .b());
endmodule

// CHECK: entity @N3 () -> () {
// CHECK:     %0 = const i32 42
// CHECK:     %a = sig i32 %0
// CHECK:     %1 = const i32 0
// CHECK:     %foo.b.default = sig i32 %1
// CHECK:     inst @X.param1 (i32$ %a) -> (i32$ %foo.b.default)
// CHECK: }
