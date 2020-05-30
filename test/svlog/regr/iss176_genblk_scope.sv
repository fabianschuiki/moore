// RUN: moore %s
// Generate blocks should have a scope.

module foo #(int N);
  if (N == 1) begin : g_toggle
    logic q;
  end else begin : g_impl
    logic [N-1:0] q, d, taps;
  end
endmodule
