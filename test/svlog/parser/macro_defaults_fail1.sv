// RUN: moore %s -E
// FAIL
// See §22.5.1 "`define".

`define MACRO3(a=5, b=0, c="C") $display(a,,b,,c);
`MACRO3
// CHECK: fatal: expected macro arguments for `MACRO3`
