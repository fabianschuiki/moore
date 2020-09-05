// RUN: moore %s -e foo -O0

module foo(input a);
    wire b = a;
endmodule

// CHECK: entity @foo (i1$ %a) -> () {
// CHECK:     %0 = const i1 0
// CHECK:     %b = sig i1 %0
// CHECK:     con i1$ %b, %a
// CHECK: }
