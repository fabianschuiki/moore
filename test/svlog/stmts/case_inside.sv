// RUN: moore %s
module foo;
  int x, y;
  localparam int MAX = 42;

  initial case (x) inside
    [0:15]: y <= 15;
    [16:MAX]: y <= x * 2;
  endcase
endmodule
