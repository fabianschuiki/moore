// RUN: moore %s -e foo -O0
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
    bar #(-a) i1();
    // CHECK: %0 = const i32 4294967254
    bar #(~a) i2();
    // CHECK: %0 = const i32 4294967253
    bar #(!a) i3();
    bar #(!z) i4();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(&z) i5();
    bar #(&w) i6();
    bar #(&x) i7();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(~&z) i8();
    bar #(~&w) i9();
    bar #(~&x) i10();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(|z) i11();
    bar #(|w) i12();
    bar #(|x) i13();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 1
    bar #(~|z) i14();
    bar #(~|w) i15();
    bar #(~|x) i16();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 0
    bar #(^a) i17();
    bar #(^b) i18();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(~^a) i19();
    bar #(~^b) i20();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(^~a) i21();
    bar #(^~b) i22();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1

    // Binary Operators

    bar #(a + b) i23();
    // CHECK: %0 = const i32 51
    bar #(a - b) i24();
    // CHECK: %0 = const i32 33
    bar #(a * b) i25();
    // CHECK: %0 = const i32 378
    bar #(a / b) i26();
    // CHECK: %0 = const i32 4
    bar #(a % b) i27();
    // CHECK: %0 = const i32 6
    bar #(a ** c) i28();
    // CHECK: %0 = const i32 74088
    bar #(a == a) i29();
    bar #(a == b) i30();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(a === a) i31();
    bar #(a === b) i32();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(a ==? a) i33();
    bar #(a ==? b) i34();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(a != a) i35();
    bar #(a != b) i36();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(a !== a) i37();
    bar #(a !== b) i38();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(a !=? a) i39();
    bar #(a !=? b) i40();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(a < a) i41();
    bar #(a < b) i42();
    bar #(b < a) i43();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(a <= a) i44();
    bar #(a <= b) i45();
    bar #(b <= a) i46();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(a > a) i47();
    bar #(a > b) i48();
    bar #(b > a) i49();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(a >= a) i50();
    bar #(a >= b) i51();
    bar #(b >= a) i52();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(a << b) i53();
    // CHECK: %0 = const i32 21504
    bar #(a <<< b) i54();
    // CHECK: %0 = const i32 21504
    bar #(d >> b) i55();
    bar #(w >> b) i56();
    // CHECK: %0 = const i32 24112
    // CHECK: %0 = const i32 8388607
    bar #(d >>> b) i57();
    bar #(w >>> b) i58();
    // CHECK: %0 = const i32 24112
    // TODO: Fix this once #142 lands
    //!CHECK: %0 = const i32 4294967295
    bar #(x & y) i59();
    bar #(x ~& y) i60();
    // CHECK: %0 = const i32 132
    // CHECK: %0 = const i32 4294967163
    bar #(x | y) i61();
    bar #(x ~| y) i62();
    // CHECK: %0 = const i32 237
    // CHECK: %0 = const i32 4294967058
    bar #(x ^ y) i63();
    bar #(x ~^ y) i64();
    bar #(x ^~ y) i65();
    // CHECK: %0 = const i32 105
    // CHECK: %0 = const i32 4294967190
    // CHECK: %0 = const i32 4294967190
    bar #(a && b) i66();
    bar #(z && b) i67();
    bar #(z && z) i68();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 0
    bar #(a || b) i69();
    bar #(z || b) i70();
    bar #(z || z) i71();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0

    // Ternary Operator

    bar #(a == b ? 42 : 9001) i72();
    bar #(a != b ? 42 : 9001) i73();
    // CHECK: %0 = const i32 9001
    // CHECK: %0 = const i32 42

    // Cast Operators

    bar #(unsigned'(a)) i74();
    bar #(signed'(a)) i75();
    bar #($unsigned(a)) i76();
    bar #($signed(a)) i77();
    // CHECK: %0 = const i32 42
    // CHECK: %0 = const i32 42
    // CHECK: %0 = const i32 42
    // CHECK: %0 = const i32 42
endmodule

module bar #(parameter int X);
    int x = X;
endmodule
