// RUN: moore %s -e foo

module foo;
  struct {
    byte a;
    byte [2:0] b;
  } z;
  assign z = '{default: '0};
endmodule
