// RUN: moore -e A --format=mlir %s | FileCheck %s

module A();
  wire [1:0][2:0] x = {3'h0, 3'h0};
endmodule
// CHECK: [[TMP:%.+]] = llhd.sig "{{[0-9]+}}" {{%.+}} : !hw.array<2xi3>
// CHECK: llhd.con %x, [[TMP]] : !llhd.sig<!hw.array<2xi3>>
