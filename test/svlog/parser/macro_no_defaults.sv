// RUN: moore %s -E
// See §22.5.1 "`define".

`define D(x,y) initial $display("start", x , y, "end");
D0: `D( "msg1" , "msg2" ) x
D1: `D( " msg1", ) x
D2: `D(, "msg2 ") x
D3: `D(,) x
D4: `D( , ) x
// CHECK: D0: initial $display("start", "msg1" , "msg2", "end"); x
// CHECK: D1: initial $display("start", " msg1" , , "end"); x
// CHECK: D2: initial $display("start",  , "msg2 ", "end"); x
// CHECK: D3: initial $display("start",  , , "end"); x
// CHECK: D4: initial $display("start",  , , "end"); x
