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
    // CHECK: %4 = extf i2$, [4 x i2]$ %b, 0
    // CHECK: %c.prb = prb i10$ %c
    // CHECK: %5 = exts i8, i10 %c.prb, 0, 8
    // CHECK: %6 = exts i2, i8 %5, 0, 2
    // CHECK: drv i2$ %4, %6, %3

    // b[1] = c[3:2]
    // CHECK: %7 = const i32 1
    // CHECK: %8 = [4 x i2 %0]
    // CHECK: %9 = sig [4 x i2] %8
    // CHECK: %10 = shr [4 x i2]$ %b, [4 x i2]$ %9, i32 %7
    // CHECK: %11 = extf i2$, [4 x i2]$ %10, 0
    // CHECK: %12 = exts i6, i8 %5, 2, 6
    // CHECK: %13 = const i8 0
    // CHECK: %14 = inss i8 %13, i6 %12, 0, 6
    // CHECK: %15 = exts i2, i8 %14, 0, 2
    // CHECK: drv i2$ %11, %15, %3

    // b[2] = c[5:4]
    // CHECK: %16 = const i32 2
    // CHECK: %17 = sig [4 x i2] %8
    // CHECK: %18 = shr [4 x i2]$ %b, [4 x i2]$ %17, i32 %16
    // CHECK: %19 = extf i2$, [4 x i2]$ %18, 0
    // CHECK: %20 = exts i4, i8 %5, 4, 4
    // CHECK: %21 = inss i8 %13, i4 %20, 0, 4
    // CHECK: %22 = exts i2, i8 %21, 0, 2
    // CHECK: drv i2$ %19, %22, %3

    // b[3] = c[7:6]
    // CHECK: %23 = const i32 3
    // CHECK: %24 = sig [4 x i2] %8
    // CHECK: %25 = shr [4 x i2]$ %b, [4 x i2]$ %24, i32 %23
    // CHECK: %26 = extf i2$, [4 x i2]$ %25, 0
    // CHECK: %27 = exts i2, i8 %5, 6, 2
    // CHECK: %28 = inss i8 %13, i2 %27, 0, 2
    // CHECK: %29 = exts i2, i8 %28, 0, 2
    // CHECK: drv i2$ %26, %29, %3

    // a = c[9:8]
    // CHECK: %30 = exts i2, i10 %c.prb, 8, 2
    // CHECK: %31 = inss i10 %2, i2 %30, 0, 2
    // CHECK: %32 = exts i2, i10 %31, 0, 2
    // CHECK: drv i2$ %a, %32, %3
endmodule
