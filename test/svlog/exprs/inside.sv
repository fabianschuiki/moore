// RUN: moore %s -e foo
module foo;
  logic [3:0] x;
  bit z;
  initial z = x inside {[3'b000:3'b100], 3'b111};
endmodule
