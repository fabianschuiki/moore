// RUN: moore %s
// FAIL
`define foo(x)
`foo (a,b)
// CHECK: fatal: macro expansion with 2 arguments, but `foo` expects 1 arguments
