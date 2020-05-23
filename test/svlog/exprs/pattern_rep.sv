// RUN: moore %s -e foo -O0
module foo;
    // Arrays
    int [1:2][1:3] n1 = '{'{0,1,2},'{3{4}}};
    // CHECK: %0 = const i32 0
    // CHECK: %1 = const i32 1
    // CHECK: %2 = const i32 2
    // CHECK: %4 = const i32 4
    // CHECK: %5 = const i32 4
    // CHECK: %6 = const i32 4
    int [1:2][1:6] n2 = '{2{'{3{4, 5}}}};
    // CHECK: %9 = const i32 4
    // CHECK: %10 = const i32 5
    // CHECK: %11 = const i32 4
    // CHECK: %12 = const i32 5
    // CHECK: %13 = const i32 4
    // CHECK: %14 = const i32 5
    // CHECK: %16 = const i32 4
    // CHECK: %17 = const i32 5
    // CHECK: %18 = const i32 4
    // CHECK: %19 = const i32 5
    // CHECK: %20 = const i32 4
    // CHECK: %21 = const i32 5

    // Structs
    // struct {int X,Y,Z;} XYZ = '{3{1}}; // not yet supported
    typedef struct {int a; int[3:0] b;} ab_t;
    int a,b,c;
    ab_t [1:0] [2:0] v1;
    initial v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};
endmodule
