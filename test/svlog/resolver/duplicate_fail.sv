// RUN: moore %s
// FAIL
module foo;
  int a;
  int a;
  // CHECK: error: `a` is defined multiple times
endmodule
