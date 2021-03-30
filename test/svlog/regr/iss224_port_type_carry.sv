// RUN: moore %s -e A

module A;
  wire [31:0] x;
  wire y;
  B system_bus_xbar (.x(x), .y(y));
endmodule

module B (input [31:0] x, output y);
endmodule
