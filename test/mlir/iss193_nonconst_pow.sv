// RUN: moore %s -e foo

module foo (input int x, output int z[10]);
    always_comb begin
        z[0] = 1 ** x;
        // CHECK: %1 = const i32 1
        // CHECK: drv i32$ %0, %1, %2
        z[1] = 2 ** x;
        // CHECK: %8 = shl i32 %1, i32 %3, i32 %x.prb
        // CHECK: drv i32$ %7, %8, %2
        z[2] = 4 ** x;
        // CHECK: %9 = const i32 2
        // CHECK: %13 = umul i32 %9, %x.prb
        // CHECK: %14 = shl i32 %1, i32 %3, i32 %13
        // CHECK: drv i32$ %12, %14, %2
        z[3] = 8 ** x;
        // CHECK: %15 = const i32 3
        // CHECK: %19 = umul i32 %15, %x.prb
        // CHECK: %20 = shl i32 %1, i32 %3, i32 %19
        // CHECK: drv i32$ %18, %20, %2
        z[4] = 16 ** x;
        // CHECK: %21 = const i32 4
        // CHECK: %25 = umul i32 %21, %x.prb
        // CHECK: %26 = shl i32 %1, i32 %3, i32 %25
        // CHECK: drv i32$ %24, %26, %2

        z[5] = x ** 1;
        // CHECK: drv i32$ %30, %x.prb, %2
        z[6] = x ** 2;
        // CHECK: %35 = umul i32 %x.prb, %x.prb
        // CHECK: drv i32$ %34, %35, %2
        z[7] = x ** 3;
        // CHECK: %40 = umul i32 %35, %x.prb
        // CHECK: drv i32$ %39, %40, %2
        z[8] = x ** 4;
        // CHECK: %45 = umul i32 %40, %x.prb
        // CHECK: drv i32$ %44, %45, %2
        z[9] = x ** 5;
        // CHECK: %50 = umul i32 %45, %x.prb
        // CHECK: drv i32$ %49, %50, %2
    end
endmodule
