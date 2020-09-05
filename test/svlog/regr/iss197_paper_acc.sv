// RUN: moore %s -e acc

module acc (input clk, input [31:0] x, input en, output [31:0] q);
    bit [31:0] d, q;
    always_ff @(posedge clk) q <= #1ns d;
    always_comb begin
        d <= #2ns q;
        if (en) d <= #2ns q+x;
    end
endmodule

// CHECK: proc %acc.always_ff.45.0 (i1$ %clk, i32$ %d) -> (i32$ %q) {
// CHECK: init:
// CHECK:     %clk.prb = prb i1$ %clk
// CHECK: check:
// CHECK:     %clk.prb1 = prb i1$ %clk
// CHECK: }
