// RUN: moore %s -e foo -O0

module foo (bar x);
	assign x.data = 42;
	assign x.valid = 1;
	assign x.ready = 0;
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;
endinterface

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) {
// CHECK:     drv i32$ %x.data, %0, %1
// CHECK:     drv i1$ %x.valid, %2, %3
// CHECK:     drv i1$ %x.ready, %4, %5
// CHECK: }
