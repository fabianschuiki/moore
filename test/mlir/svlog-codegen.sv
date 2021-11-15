// RUN: moore -e Foo --format=mlir-native %s | FileCheck %s

// CHECK-LABEL: llhd.entity @Foo (
// CHECK-SAME:    [[ARG_X:%.+]] : !llhd.sig<i1>,
// CHECK-SAME:    [[ARG_Z:%.+]] : !llhd.sig<i3>
// CHECK-SAME:  ) -> (
// CHECK-SAME:    [[ARG_Y:%.+]] : !llhd.sig<i2>,
// CHECK-SAME:    [[ARG_UNDRIVEN_OUTPUT0:%.+]] : !llhd.sig<i4>
// CHECK-SAME:    [[ARG_UNDRIVEN_OUTPUT1:%.+]] : !llhd.sig<i5>
// CHECK-SAME:  ) {
module Foo (
    input bit x,
    output bit [1:0] y = 3,
    input bit [2:0] z,
    output bit [3:0] undriven_output0,
    output bit [4:0] undriven_output1 = 9
);
    // Declarations
    bit a = 0;
    wire bit b = a;
    // CHECK: [[DECL_A:%.+]] = llhd.sig "a" %false : i1
    // CHECK: [[DECL_B:%.+]] = llhd.sig "b" {{.+}} : i1
    // CHECK: llhd.con [[DECL_B]], [[DECL_A]] : !llhd.sig<i1>

    // Undriven outputs are driven with a default value.
    // CHECK: [[TMP:%.+]] = hw.constant 0 : i4
    // CHECK-NEXT: [[TIME:%.+]] = llhd.constant_time
    // CHECK-NEXT: llhd.drv [[ARG_UNDRIVEN_OUTPUT0]], [[TMP]] after [[TIME]] : !llhd.sig<i4>
    // CHECK: [[TMP:%.+]] = hw.constant 9 : i5
    // CHECK-NEXT: [[TIME:%.+]] = llhd.constant_time
    // CHECK-NEXT: llhd.drv [[ARG_UNDRIVEN_OUTPUT1]], [[TMP]] after [[TIME]] : !llhd.sig<i5>
endmodule
// CHECK: }
