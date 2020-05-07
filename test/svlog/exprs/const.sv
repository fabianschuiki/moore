// RUN: moore %s -e foo
module foo;
    localparam int a = 42;
    localparam int b = 9;
    localparam int c = 3;
    localparam int d = 12345678;
    localparam int x = 8'b10100101;
    localparam int y = 8'b11001100;
    localparam int z = 0;
    localparam int w = 32'hffffffff;

    // Unary Operators

    bar #(+a) i0();
    // CHECK: %0 = const i32 42
    bar #(-a) i0();
    // CHECK: %0 = const i32 -42
    bar #(~a) i0();
    // CHECK: %0 = const i32 4294967253
    // TODO: Fix these to i32 once #141 lands.
    bar #(!a) i0();
    bar #(!z) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    bar #(&z) i0();
    bar #(&w) i0();
    bar #(&x) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    bar #(~&z) i0();
    bar #(~&w) i0();
    bar #(~&x) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    bar #(|z) i0();
    bar #(|w) i0();
    bar #(|x) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 1
    bar #(~|z) i0();
    bar #(~|w) i0();
    bar #(~|x) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 0
    bar #(^a) i0();
    bar #(^b) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    bar #(~^a) i0();
    bar #(~^b) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    bar #(^~a) i0();
    bar #(^~b) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1

    // Binary Operators

    bar #(a + b) i0();
    // CHECK: %0 = const i32 51
    bar #(a - b) i0();
    // CHECK: %0 = const i32 33
    bar #(a * b) i0();
    // CHECK: %0 = const i32 378
    bar #(a / b) i0();
    // CHECK: %0 = const i32 4
    bar #(a % b) i0();
    // CHECK: %0 = const i32 6
    bar #(a ** c) i0();
    // CHECK: %0 = const i32 74088
    // TODO: Fix these to i32 once #141 lands.
    bar #(a == a) i0();
    bar #(a == b) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    bar #(a === a) i0();
    bar #(a === b) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    bar #(a ==? a) i0();
    bar #(a ==? b) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    bar #(a != a) i0();
    bar #(a != b) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    bar #(a !== a) i0();
    bar #(a !== b) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    bar #(a !=? a) i0();
    bar #(a !=? b) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    bar #(a < a) i0();
    bar #(a < b) i0();
    bar #(b < a) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    bar #(a <= a) i0();
    bar #(a <= b) i0();
    bar #(b <= a) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    bar #(a > a) i0();
    bar #(a > b) i0();
    bar #(b > a) i0();
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    bar #(a >= a) i0();
    bar #(a >= b) i0();
    bar #(b >= a) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    bar #(a << b) i0();
    // CHECK: %0 = const i32 21504
    bar #(a <<< b) i0();
    // CHECK: %0 = const i32 21504
    bar #(d >> b) i0();
    bar #(w >> b) i0();
    // CHECK: %0 = const i32 24112
    // CHECK: %0 = const i32 8388607
    bar #(d >>> b) i0();
    bar #(w >>> b) i0();
    // CHECK: %0 = const i32 24112
    // TODO: Fix this once #142 lands
    //!CHECK: %0 = const i32 4294967295
    bar #(x & y) i0();
    bar #(x ~& y) i0();
    // CHECK: %0 = const i32 132
    // CHECK: %0 = const i32 4294967163
    bar #(x | y) i0();
    bar #(x ~| y) i0();
    // CHECK: %0 = const i32 237
    // CHECK: %0 = const i32 4294967058
    bar #(x ^ y) i0();
    bar #(x ~^ y) i0();
    bar #(x ^~ y) i0();
    // CHECK: %0 = const i32 105
    // CHECK: %0 = const i32 4294967190
    // CHECK: %0 = const i32 4294967190
    bar #(a && b) i0();
    bar #(z && b) i0();
    bar #(z && z) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0
    // CHECK: %0 = const i1 0
    bar #(a || b) i0();
    bar #(z || b) i0();
    bar #(z || z) i0();
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 1
    // CHECK: %0 = const i1 0

    // Ternary Operator

    bar #(a == b ? 42 : 9001) i0();
    bar #(a != b ? 42 : 9001) i0();
    // CHECK: %0 = const i32 9001
    // CHECK: %0 = const i32 42

    // Cast Operators

    bar #(unsigned'(a)) i0();
    bar #(signed'(a)) i0();
    bar #($unsigned(a)) i0();
    bar #($signed(a)) i0();
    // CHECK: %0 = const i32 42
    // CHECK: %0 = const i32 42
    // CHECK: %0 = const i32 42
    // CHECK: %0 = const i32 42
endmodule

module bar #(parameter int X);
    int x = X;
endmodule
