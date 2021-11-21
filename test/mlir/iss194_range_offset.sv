// RUN: moore %s -e foo -e bar

// CHECK: entity @foo (i8$ %x) -> (i8$ %z) {
module foo (input logic [8:1] x, output logic [2:9] z);
    assign z = x;
    // CHECK: %x.prb = prb i8$ %x
    // CHECK: drv i8$ %z, %x.prb, %1

    logic b0, b1, b2, b3;
    assign b0 = x[1];
    // CHECK: %2 = exts i1, i8 %x.prb, 0, 1
    // CHECK: drv i1$ %b0, %2, %1
    assign b1 = x[8];
    // CHECK: %3 = exts i1, i8 %x.prb, 7, 1
    // CHECK: drv i1$ %b1, %6, %1
    assign b2 = z[2];
    // CHECK: %z.prb = prb i8$ %z
    // CHECK: %7 = exts i1, i8 %z.prb, 0, 1
    // CHECK: drv i1$ %b2, %7, %1
    assign b3 = z[9];
    // CHECK: %8 = exts i1, i8 %z.prb, 7, 1
    // CHECK: drv i1$ %b3, %10, %1
endmodule
// CHECK: }

// CHECK: entity @bar (i1$ %b0, i1$ %b1, i1$ %b2, i1$ %b3) -> () {
module bar (input logic b0, b1, b2, b3);
    logic [8:1] x;
    logic [2:9] z;
    assign x[1] = b0;
    // CHECK: %2 = exts i1$, i8$ %x, 0, 1
    // CHECK: %b0.prb = prb i1$ %b0
    // CHECK: drv i1$ %2, %b0.prb, %1
    assign x[8] = b1;
    // CHECK: %3 = const i32 7
    // CHECK: %5 = shr i8$ %x, i8$ %4, i32 %3
    // CHECK: %6 = exts i1$, i8$ %5, 0, 1
    // CHECK: %b1.prb = prb i1$ %b1
    // CHECK: drv i1$ %6, %b1.prb, %1
    assign z[2] = b2;
    // CHECK: %7 = exts i1$, i8$ %z, 0, 1
    // CHECK: %b2.prb = prb i1$ %b2
    // CHECK: drv i1$ %7, %b2.prb, %1
    assign z[9] = b3;
    // CHECK: %9 = shr i8$ %z, i8$ %8, i32 %3
    // CHECK: %10 = exts i1$, i8$ %9, 0, 1
    // CHECK: %b3.prb = prb i1$ %b3
    // CHECK: drv i1$ %10, %b3.prb, %1
endmodule
// CHECK: }
