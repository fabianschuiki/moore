// RUN: moore %s -e foo -O0
module foo;
    localparam string a = "foo";
    localparam string b = "bar";

    bar #(a) i0();
    baz #(a) i1();
    // CHECK: %0 = const i32 6713199
    // CHECK: %0 = const i16 28527
    bar #(b) i2();
    baz #(b) i3();
    // CHECK: %0 = const i32 6447474
    // CHECK: %0 = const i16 24946

    bar #(a == a) i4();
    bar #(a == b) i5();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(a === a) i6();
    bar #(a === b) i7();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(a ==? a) i8();
    bar #(a ==? b) i9();
    // CHECK: %0 = const i32 1
    // CHECK: %0 = const i32 0
    bar #(a != a) i10();
    bar #(a != b) i11();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(a !== a) i12();
    bar #(a !== b) i13();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
    bar #(a !=? a) i14();
    bar #(a !=? b) i15();
    // CHECK: %0 = const i32 0
    // CHECK: %0 = const i32 1
endmodule

module bar #(parameter int X);
    int x = X;
endmodule

module baz #(parameter shortint X);
    shortint x = X;
endmodule
