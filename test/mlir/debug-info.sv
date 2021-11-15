// RUN: moore -e A --format=mlir-native -g %s | FileCheck %s

module A;
endmodule
// CHECK: llhd.entity @A () -> () {
// CHECK-NEXT: } loc([[LOC:#.+]])
// CHECK: [[LOC]] = loc("{{.+}}/debug-info.sv":3:1)
