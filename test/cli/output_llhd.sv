// RUN: moore %s -e foo --format llhd

module foo (output int x);
    initial x = 42;
endmodule

// CHECK: proc %foo.initial.15.0 () -> (i32$ %x) {
// CHECK: 0:
// CHECK:     %1 = const i32 42
// CHECK:     %2 = const time 0s 1e
// CHECK:     drv i32$ %x, %1, %2
// CHECK:     halt
// CHECK: }
// CHECK:
// CHECK: entity @foo () -> (i32$ %x) {
// CHECK:     inst %foo.initial.15.0 () -> (i32$ %x)
// CHECK: }
