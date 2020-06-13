// RUN: moore %s -e foo -O0

module foo (bar x, bar y[3:0]);
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;
endinterface

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready, [4 x i32]$ %y.data, [4 x i1]$ %y.valid, [4 x i1]$ %y.ready) {
// CHECK: }
