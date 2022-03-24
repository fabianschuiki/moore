// RUN: moore %s -e foo --format=mlir-native

module foo;
    initial #42;
    // CHECK: %0 = llhd.constant_time <42000ps, 0d, 0e>
endmodule
