// RUN: moore %s -e foo -O0

module foo (bar x);
	fee u0(x);
endmodule

module fee (bar x);
    assign x.data = 42;
    assign x.valid = 1;
    assign x.ready = 0;
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;
endinterface

// CHECK: entity @fee.param3 () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) {
// CHECK:     drv i32$ %x.data, %1, %0
// CHECK:     drv i1$ %x.valid, %3, %2
// CHECK:     drv i1$ %x.ready, %5, %4
// CHECK: }

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) {
// CHECK:     inst @fee.param3 () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready)
// CHECK: }
