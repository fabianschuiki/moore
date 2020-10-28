// RUN: moore %s -e foo -O0

module foo;
    bar #(32, logic) x();
    bar #(19, byte) y();

    assign x.data = 9001;
    assign y.data = 9001;

    assign x.valid = 1;
    assign y.valid = 1;

    logic [31:0] xd;
    logic [18:0] yd;
    assign xd = x.data;
    assign yd = y.data;

    int xwd = $bits(x.data);
    int xwv = $bits(x.valid);
    int ywd = $bits(y.data);
    int ywv = $bits(y.valid);

    initial begin
        int xwd = $bits(x.data);
        int xwv = $bits(x.valid);
        int ywd = $bits(y.data);
        int ywv = $bits(y.valid);
    end
endmodule

interface bar #(
    parameter int N,
    parameter type T
);
    logic [N-1:0] data;
    T valid;
    logic ready;
endinterface

// CHECK: proc %foo.initial.229.0 () -> () {
// CHECK:     %1 = const i32 32
// CHECK:     %2 = const i32 1
// CHECK:     %3 = const i32 19
// CHECK:     %4 = const i32 8
// CHECK: }

// CHECK: entity @foo () -> () {
// CHECK:     %x.data = sig i32 %6
// CHECK:     %x.valid = sig i1 %7
// CHECK:     %x.ready = sig i1 %8
// CHECK:     %y.data = sig i19 %9
// CHECK:     %y.valid = sig i8 %10
// CHECK:     %y.ready = sig i1 %11
// CHECK:     %13 = const i32 9001
// CHECK:     %15 = const i19 9001
// CHECK:     %17 = const i1 1
// CHECK:     %19 = const i8 1
// CHECK: }
