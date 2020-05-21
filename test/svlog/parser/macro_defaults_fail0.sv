// RUN: moore %s -E
// FAIL
// See §22.5.1 "`define".

`define MACRO1(a=5,b="B",c) $display(a,,b,,c);
`MACRO1 ( 1 )
// CHECK: fatal: macro expansion missing value for `c`
