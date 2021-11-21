// RUN: moore %s -e A0

module A0;
    int x;
    A1 i1(x);
    A1 #(0) i2(x);
    A1 #(1) i3(x);
endmodule

module A1 #(int K = 0) (output int k = K);
endmodule

// CHECK: entity @A1.param1 () -> (i32$ %k) {
// CHECK:     %0 = const i32 0
// CHECK:     %1 = const time 0s
// CHECK:     drv i32$ %k, %0, %1
// CHECK: }
// CHECK:
// CHECK: entity @A1.param2 () -> (i32$ %k) {
// CHECK:     %0 = const i32 0
// CHECK:     %1 = const time 0s
// CHECK:     drv i32$ %k, %0, %1
// CHECK: }
// CHECK:
// CHECK: entity @A1.param3 () -> (i32$ %k) {
// CHECK:     %0 = const i32 1
// CHECK:     %1 = const time 0s
// CHECK:     drv i32$ %k, %0, %1
// CHECK: }
