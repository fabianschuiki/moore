// RUN: moore %s -e foo -O0

module foo;
    int v0 = $clog2(0);
    // CHECK: %0 = const i32 0
    int v1 = $clog2(1);
    // CHECK: %1 = const i32 0
    int v2 = $clog2(2);
    // CHECK: %2 = const i32 1
    int v3 = $clog2(3);
    // CHECK: %3 = const i32 2
    int v4 = $clog2(4);
    // CHECK: %4 = const i32 2
    int v5 = $clog2(5);
    // CHECK: %5 = const i32 3
    int v6 = $clog2(6);
    // CHECK: %6 = const i32 3
    int v7 = $clog2(7);
    // CHECK: %7 = const i32 3
    int v8 = $clog2(8);
    // CHECK: %8 = const i32 3
    int v9 = $clog2(9);
    // CHECK: %9 = const i32 4
endmodule
