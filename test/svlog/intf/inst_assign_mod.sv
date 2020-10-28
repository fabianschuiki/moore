// RUN: moore %s -e foo -O0

module foo;
	bar x();
	assign x.data = 42;
	assign x.valid = 1;
	assign x.ready = 0;
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;
endinterface

// CHECK: entity @foo () -> () {
// CHECK:     %x.data = sig i32 %0
// CHECK:     %x.valid = sig i1 %1
// CHECK:     %x.ready = sig i1 %2
// CHECK:     drv i32$ %x.data, %4, %3
// CHECK:     drv i1$ %x.valid, %6, %5
// CHECK:     drv i1$ %x.ready, %8, %7
// CHECK: }
