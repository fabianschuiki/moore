// RUN: moore %s -e foo -O0

module foo;
    int v0 = $isunknown(4'b0101);
    // CHECK: %0 = const i32 0
endmodule
