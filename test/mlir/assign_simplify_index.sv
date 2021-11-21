// RUN: moore %s -e foo

module foo;
    logic [7:0] a;
    logic [3:0] b;
    initial begin
        {a, b}[0] = 1;
        // CHECK: %1 = exts i1$, i4$ %b, 0, 1
        // CHECK: %2 = const i1 1
        // CHECK: %3 = const time 0s 1e
        // CHECK: drv i1$ %1, %2, %3
        // CHECK: %4 = const i32 4294967292
        // CHECK: %5 = const i8 0
        // CHECK: %6 = sig i8 %5
        // CHECK: %7 = shr i8$ %a, i8$ %6, i32 %4
        // CHECK: %8 = exts i1$, i8$ %7, 0, 1
        // CHECK: drv i1$ %8, %2, %3
        {a, b}[4] = 1;
        // CHECK: %9 = const i32 4
        // CHECK: %10 = const i4 0
        // CHECK: %11 = sig i4 %10
        // CHECK: %12 = shr i4$ %b, i4$ %11, i32 %9
        // CHECK: %13 = exts i1$, i4$ %12, 0, 1
        // CHECK: drv i1$ %13, %2, %3
        // CHECK: %14 = exts i1$, i8$ %a, 0, 1
        // CHECK: drv i1$ %14, %2, %3
    end
endmodule
