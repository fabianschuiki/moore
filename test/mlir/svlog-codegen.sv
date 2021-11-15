// RUN: moore -e Foo --format=mlir-native %s | FileCheck %s

// CHECK-LABEL: llhd.entity @Foo (
// CHECK-SAME:    [[ARG_X:%.+]]: !llhd.sig<i1>,
// CHECK-SAME:    [[ARG_Z:%.+]]: !llhd.sig<i3>
// CHECK-SAME:  ) -> (
// CHECK-SAME:    [[ARG_Y:%.+]]: !llhd.sig<i2>
// CHECK-SAME:  ) {
// CHECK-NEXT:  }
module Foo (
    input bit x,
    output bit [1:0] y,
    input bit [2:0] z
);
endmodule
