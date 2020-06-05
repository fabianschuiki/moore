// RUN: moore %s -e foo -O0
module foo;
    struct packed {
        byte a;
        int b;
        struct packed {
            shortint x;
            longint y;
        } c;
    } p;
    int [3:0] q;

    initial begin
        p = '{1, 42, '{1337, 9001}};
        // CHECK: %1 = const i8 1
        // CHECK: %2 = const i32 42
        // CHECK: %3 = const i16 1337
        // CHECK: %4 = const i64 9001
        q = '{1, 2, 3, 4};
        // CHECK: %8 = const i32 1
        // CHECK: %9 = const i32 2
        // CHECK: %10 = const i32 3
        // CHECK: %11 = const i32 4
    end
endmodule
