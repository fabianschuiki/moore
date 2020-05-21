// RUN: moore %s -E
// See §22.5.1 "`define".

`define A0(a=5)
`define A1(a =5)
`define A2(a= 5)
`define A3(a = 5)
`define A4(a=)
`define A5(a =)
`define A6(a= )
`define A7(a = )

`define MACRO1(a=5,b="B",c) $display(a,,b,,c);
M1A: `MACRO1 ( , 2, 3 ) x
M1B: `MACRO1 ( 1 , , 3 ) x
M1C: `MACRO1 ( , 2, ) x
// CHECK: M1A: $display(5,,2,,3); x
// CHECK: M1B: $display(1,,"B",,3); x
// CHECK: M1C: $display(5,,2,,); x

`define MACRO2(a=5, b, c="C") $display(a,,b,,c);
M2A: `MACRO2 (1, , 3) x
M2B: `MACRO2 (, 2, ) x
M2C: `MACRO2 (, 2) x
// CHECK: M2A: $display(1,,,,3); x
// CHECK: M2B: $display(5,,2,,"C"); x
// CHECK: M2C: $display(5,,2,,"C"); x

`define MACRO3(a=5, b=0, c="C") $display(a,,b,,c);
M3A: `MACRO3 ( 1 ) x
M3B: `MACRO3 ( ) x
// CHECK: M3A: $display(1,,0,,"C"); x
// CHECK: M3B: $display(5,,0,,"C"); x
