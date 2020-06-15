// RUN: moore %s -e foo -O0

module foo (input logic clk, output logic clk_out);
    bar x(clk, clk_out);
    assign x.clk_out = ~x.clk;
endmodule

interface bar (input logic clk, output logic clk_out);
    logic [31:0] data;
    logic valid;
    logic ready;
endinterface

// CHECK: entity @foo (i1$ %clk) -> (i1$ %clk_out) {
// CHECK:     %x.clk = sig i1 %0
// CHECK:     %x.clk_out = sig i1 %1
// CHECK:     %x.data = sig i32 %2
// CHECK:     %x.valid = sig i1 %3
// CHECK:     %x.ready = sig i1 %4
// CHECK:     con i1$ %x.clk, %6
// CHECK:     con i1$ %x.clk_out, %clk_out
// CHECK: }
