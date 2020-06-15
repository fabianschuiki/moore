// RUN: moore %s -e foo -O0

module foo;
    bar #(32, logic) x();
    bar #(19, byte) y();

    assign x.data = 9001;
    assign y.data = 9001;

    assign x.valid = 1;
    assign y.valid = 1;
endmodule

interface bar #(
    parameter int N,
    parameter type T
);
    logic [N-1:0] data;
    T valid;
    logic ready;
endinterface

// CHECK: entity @foo () -> () {
// CHECK:     %x.data = sig i32 %0
// CHECK:     %x.valid = sig i1 %1
// CHECK:     %x.ready = sig i1 %2
// CHECK:     %y.data = sig i19 %3
// CHECK:     %y.valid = sig i8 %4
// CHECK:     %y.ready = sig i1 %5
// CHECK:     %6 = const i32 9001
// CHECK:     %8 = const i19 9001
// CHECK:     %10 = const i1 1
// CHECK:     %12 = const i8 1
// CHECK: }
