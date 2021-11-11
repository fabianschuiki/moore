// RUN: moore %s -e foo
module foo;
  logic [1:0] x;
  logic y;
  wire [5:0] z = y ? 6'h0 : |x;
  // In the above, the compiler used to report an rvalue lowering error where
  // `|x` would have operation type `logic [5:0]`, but the argument would be of
  // type `logic [1:0]`. The correct operation type is `logic [1:0]`.
endmodule
