// RUN: moore %s -e foo -O0

module foo (bar.in x, bar.out y);
	initial begin
		y.data = x.data;
		y.valid = x.valid;
		x.ready = y.ready;
	end
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;

    modport in (input data, valid, output ready);
    modport out (output data, valid, input ready);
endinterface

// CHECK: proc %foo.initial.84.0 (i32$ %x.data, i1$ %x.valid, i1$ %y.ready) -> (i1$ %x.ready, i32$ %y.data, i1$ %y.valid) {
// CHECK:     drv i32$ %y.data, %x.data1, %1
// CHECK:     drv i1$ %y.valid, %x.valid1, %2
// CHECK:     drv i1$ %x.ready, %y.ready1, %3
// CHECK: }

// CHECK: entity @foo (i32$ %x.data, i1$ %x.valid, i1$ %y.ready) -> (i1$ %x.ready, i32$ %y.data, i1$ %y.valid) {
// CHECK:     inst %foo.initial.84.0 (i32$ %x.data, i1$ %x.valid, i1$ %y.ready) -> (i1$ %x.ready, i32$ %y.data, i1$ %y.valid)
// CHECK: }
