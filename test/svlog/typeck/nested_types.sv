// RUN: moore %s -e foo -Vtypes
module foo;
  typedef int fizz;
  typedef fizz [15:0] buzz;
  int x0;
  fizz x1;
  fizz [3:0] x2;
  buzz [3:0] x3;

  initial begin
    int x;
    x = x0;
    x = x1;
    x = x2;
    x = x3;
  end
endmodule
