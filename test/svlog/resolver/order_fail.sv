// RUN: moore %s
// FAIL
module foo;
  int b = a;
  int a;
  // CHECK: error: `a` not found
endmodule
