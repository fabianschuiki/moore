// RUN: moore %s -e A --format=mlir

module A();
  wire [1:0][2:0] x = {3'h0, 3'h0};
endmodule
// CHECK: %x = llhd.sig "x" %1 : !hw.array<2xi3>
// CHECK: %3 = llhd.sig "3" %2 : !hw.array<2xi3>
// CHECK: llhd.con %x, %3 : !llhd.sig<!hw.array<2xi3>>
