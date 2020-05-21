// RUN: moore %s -E
// FAIL
// See §22.5.1 "`define".

`define D(x,y) initial $display("start", x , y, "end");
`D("msg1")
// CHECK: fatal: macro expansion missing value for `y`
