// RUN: moore %s -e foo

module foo;
    logic [1:0]      a; // 2 bits
    logic [3:0][1:0] b; // 8 bits
    logic [9:0]      c; // 10 bits

    assign {a, b} = c;

    // CHECK: %0 = const i2 0
    // CHECK: %a = sig i2 %0
    // CHECK: %1 = [i2 %0, %0, %0, %0]
    // CHECK: %b = sig [4 x i2] %1
    // CHECK: %2 = const i10 0
    // CHECK: %c = sig i10 %2
    // CHECK: %3 = const time 0s 1e

    // b[0] = c[1:0]
    // CHECK: %4 = const i32 3
    // CHECK: %5 = [4 x i2 %0]
    // CHECK: %6 = sig [4 x i2] %5
    // CHECK: %7 = shr [4 x i2]$ %b, [4 x i2]$ %6, i32 %4
    // CHECK: %8 = extf i2$, [4 x i2]$ %7, 0
    // CHECK: %c.prb = prb i10$ %c
    // CHECK: %9 = exts i8, i10 %c.prb, 0, 8
    // CHECK: %10 = exts i2, i8 %9, 0, 2
    // CHECK: drv i2$ %8, %10, %3

    // b[1] = c[3:2]
    // CHECK: %11 = const i32 2
    // CHECK: %12 = sig [4 x i2] %5
    // CHECK: %13 = shr [4 x i2]$ %b, [4 x i2]$ %12, i32 %11
    // CHECK: %14 = extf i2$, [4 x i2]$ %13, 0
    // CHECK: %15 = exts i6, i8 %9, 2, 6
    // CHECK: %16 = const i8 0
    // CHECK: %17 = inss i8 %16, i6 %15, 0, 6
    // CHECK: %18 = exts i2, i8 %17, 0, 2
    // CHECK: drv i2$ %14, %18, %3

    // b[2] = c[5:4]
    // CHECK: %19 = const i32 1
    // CHECK: %20 = sig [4 x i2] %5
    // CHECK: %21 = shr [4 x i2]$ %b, [4 x i2]$ %20, i32 %19
    // CHECK: %22 = extf i2$, [4 x i2]$ %21, 0
    // CHECK: %23 = exts i4, i8 %9, 4, 4
    // CHECK: %24 = inss i8 %16, i4 %23, 0, 4
    // CHECK: %25 = exts i2, i8 %24, 0, 2
    // CHECK: drv i2$ %22, %25, %3

    // b[3] = c[7:6]
    // CHECK: %26 = extf i2$, [4 x i2]$ %b, 0
    // CHECK: %27 = exts i2, i8 %9, 6, 2
    // CHECK: %28 = inss i8 %16, i2 %27, 0, 2
    // CHECK: %29 = exts i2, i8 %28, 0, 2
    // CHECK: drv i2$ %26, %29, %3

    // a = c[9:8]
    // CHECK: %30 = exts i2, i10 %c.prb, 8, 2
    // CHECK: %31 = inss i10 %2, i2 %30, 0, 2
    // CHECK: %32 = exts i2, i10 %31, 0, 2
    // CHECK: drv i2$ %a, %32, %3
endmodule
