// RUN: moore %s -e foo -O0
module foo;
    wire (highz1, pull0) bar;
endmodule

// CHECK: entity @foo () -> () {
// CHECK:     %0 = const i1 0
// CHECK:     %bar = sig i1 %0
// CHECK: }
