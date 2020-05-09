// RUN: moore %s -e A -e B -e C -e D -e E

module A;
endmodule

// CHECK: entity @A () -> () {
// CHECK: }


module B (
    input bit x,
    output bit y,
    inout bit z
);
endmodule

// CHECK: entity @B (i1$ %x) -> (i1$ %y, i1$ %z) {
// CHECK:     %0 = const i1 0
// CHECK:     drv i1$ %y, %0, %1
// CHECK:     %2 = const i1 0
// CHECK:     drv i1$ %z, %2, %3
// CHECK: }


module C (
    output bit x = 0,
    output bit y = 1
);
endmodule

// See issue #132.
// CHECK: entity @C () -> (i1$ %x, i1$ %y) {
//!CHECK:     %0 = const i1 0
// CHECK:     drv i1$ %x, %0, %1
//!CHECK:     %2 = const i1 1
// CHECK:     drv i1$ %y, %2, %3
// CHECK: }


module D (
	input bit x,
	output bit y
);
	initial y = ~x;
endmodule

// CHECK: proc %D.initial.250.0 (i1$ %x) -> (i1$ %y) {
// CHECK: 0:
// CHECK:     %x1 = prb i1$ %x
// CHECK:     %1 = not i1 %x1
// CHECK:     %2 = const time 0s 1e
// CHECK:     drv i1$ %y, %1, %2
// CHECK:     halt
// CHECK: }
// CHECK:
// CHECK: entity @D (i1$ %x) -> (i1$ %y) {
// CHECK:     inst %D.initial.250.0 (i1$ %x) -> (i1$ %y)
// CHECK: }


module E (
    input x,
    input [2:0] y = 42
);
endmodule

// CHECK: entity @E (i1$ %x, i3$ %y) -> () {
// CHECK: }
