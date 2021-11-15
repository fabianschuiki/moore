// RUN: moore -e Empty --format=mlir-native %s | FileCheck %s

// CHECK-LABEL: llhd.entity @Empty () -> () {
// CHECK-NEXT:  }
module Empty;
endmodule
