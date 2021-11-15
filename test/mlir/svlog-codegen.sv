// RUN: moore -e Empty -e Inputs --format=mlir-native %s | FileCheck %s

// CHECK-LABEL: llhd.entity @Empty () -> () {
// CHECK-NEXT:  }
module Empty;
endmodule

// CHECK-LABEL: llhd.entity @Inputs (%x: !llhd.sig<i1>, %y: !llhd.sig<i3>) -> () {
// CHECK-NEXT:  }
module Inputs(
    input bit x,
    input bit [2:0] y
);
endmodule
