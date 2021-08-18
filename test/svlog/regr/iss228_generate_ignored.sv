// RUN: moore %s -e A
// Things in a `generate` block should make their way to the output.

module A #(parameter N = 1);
  generate
    for (genvar i = 0; i < N; i++) begin
      // CHECK: inst @B.param1 () -> ()
      B b ();
    end
  endgenerate
endmodule

module B;
endmodule
