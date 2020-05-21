// RUN: moore %s -e foo -O0
module foo;
    typedef int T;
    byte x;
    type(x) y;
    type(int) z;
    type(T) w;
endmodule

// CHECK: entity @foo () -> () {
// CHECK:     %x = sig i8 %0
// CHECK:     %y = sig i8 %1
// CHECK:     %z = sig i32 %2
// CHECK:     %w = sig i32 %3
// CHECK: }
