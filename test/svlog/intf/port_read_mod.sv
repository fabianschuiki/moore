// RUN: moore %s -e foo -O0

module foo (bar x);
	logic z;
	assign z = x.valid & x.ready | !x.data;
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;
endinterface

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) {
// CHECK:     %1 = and i1 %x.valid1, %x.ready1
// CHECK:     %3 = neq i32 %x.data1, %2
// CHECK: }
