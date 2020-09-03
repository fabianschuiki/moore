// RUN: moore %s -e foo -O0

typedef bit [3:0][2:1] packed_reg;

module foo(
    // Dimension numbers:
    //          3    4        1    2
    input bit [3:0][2:1] n0 [1:5][2:8],
    input packed_reg n1 [1:5][2:8]
);
    int l00 = $left(n0);
    int l10 = $left(n1);
    // CHECK: %0 = const i32 1
    // CHECK: %1 = const i32 1
    int l01 = $left(n0, 1);
    int l11 = $left(n1, 1);
    // CHECK: %2 = const i32 1
    // CHECK: %3 = const i32 1
    int l02 = $left(n0, 2);
    int l12 = $left(n1, 2);
    // CHECK: %4 = const i32 2
    // CHECK: %5 = const i32 2
    int l03 = $left(n0, 3);
    int l13 = $left(n1, 3);
    // CHECK: %6 = const i32 3
    // CHECK: %7 = const i32 3
    int l04 = $left(n0, 4);
    int l14 = $left(n1, 4);
    // CHECK: %8 = const i32 2
    // CHECK: %9 = const i32 2

    int r00 = $right(n0);
    int r10 = $right(n1);
    // CHECK: %10 = const i32 5
    // CHECK: %11 = const i32 5
    int r01 = $right(n0, 1);
    int r11 = $right(n1, 1);
    // CHECK: %12 = const i32 5
    // CHECK: %13 = const i32 5
    int r02 = $right(n0, 2);
    int r12 = $right(n1, 2);
    // CHECK: %14 = const i32 8
    // CHECK: %15 = const i32 8
    int r03 = $right(n0, 3);
    int r13 = $right(n1, 3);
    // CHECK: %16 = const i32 0
    // CHECK: %17 = const i32 0
    int r04 = $right(n0, 4);
    int r14 = $right(n1, 4);
    // CHECK: %18 = const i32 1
    // CHECK: %19 = const i32 1

    int lo00 = $low(n0);
    int lo10 = $low(n1);
    // CHECK: %20 = const i32 1
    // CHECK: %21 = const i32 1
    int lo01 = $low(n0, 1);
    int lo11 = $low(n1, 1);
    // CHECK: %22 = const i32 1
    // CHECK: %23 = const i32 1
    int lo02 = $low(n0, 2);
    int lo12 = $low(n1, 2);
    // CHECK: %24 = const i32 2
    // CHECK: %25 = const i32 2
    int lo03 = $low(n0, 3);
    int lo13 = $low(n1, 3);
    // CHECK: %26 = const i32 0
    // CHECK: %27 = const i32 0
    int lo04 = $low(n0, 4);
    int lo14 = $low(n1, 4);
    // CHECK: %28 = const i32 1
    // CHECK: %29 = const i32 1

    int hi00 = $high(n0);
    int hi10 = $high(n1);
    // CHECK: %30 = const i32 5
    // CHECK: %31 = const i32 5
    int hi01 = $high(n0, 1);
    int hi11 = $high(n1, 1);
    // CHECK: %32 = const i32 5
    // CHECK: %33 = const i32 5
    int hi02 = $high(n0, 2);
    int hi12 = $high(n1, 2);
    // CHECK: %34 = const i32 8
    // CHECK: %35 = const i32 8
    int hi03 = $high(n0, 3);
    int hi13 = $high(n1, 3);
    // CHECK: %36 = const i32 3
    // CHECK: %37 = const i32 3
    int hi04 = $high(n0, 4);
    int hi14 = $high(n1, 4);
    // CHECK: %38 = const i32 2
    // CHECK: %39 = const i32 2

    int i00 = $increment(n0);
    int i10 = $increment(n1);
    // CHECK: %40 = const i32 1
    // CHECK: %41 = const i32 1
    int i01 = $increment(n0, 1);
    int i11 = $increment(n1, 1);
    // CHECK: %42 = const i32 1
    // CHECK: %43 = const i32 1
    int i02 = $increment(n0, 2);
    int i12 = $increment(n1, 2);
    // CHECK: %44 = const i32 1
    // CHECK: %45 = const i32 1
    int i03 = $increment(n0, 3);
    int i13 = $increment(n1, 3);
    // CHECK: %46 = const i32 4294967295
    // CHECK: %47 = const i32 4294967295
    int i04 = $increment(n0, 4);
    int i14 = $increment(n1, 4);
    // CHECK: %48 = const i32 4294967295
    // CHECK: %49 = const i32 4294967295

    int s00 = $size(n0);
    int s10 = $size(n1);
    // CHECK: %50 = const i32 5
    // CHECK: %51 = const i32 5
    int s01 = $size(n0, 1);
    int s11 = $size(n1, 1);
    // CHECK: %52 = const i32 5
    // CHECK: %53 = const i32 5
    int s02 = $size(n0, 2);
    int s12 = $size(n1, 2);
    // CHECK: %54 = const i32 7
    // CHECK: %55 = const i32 7
    int s03 = $size(n0, 3);
    int s13 = $size(n1, 3);
    // CHECK: %56 = const i32 4
    // CHECK: %57 = const i32 4
    int s04 = $size(n0, 4);
    int s14 = $size(n1, 4);
    // CHECK: %58 = const i32 2
    // CHECK: %59 = const i32 2
endmodule
