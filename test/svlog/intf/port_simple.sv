// RUN: moore %s -e foo -O0

module foo (bar x);
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;
endinterface

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) {
// CHECK: }
