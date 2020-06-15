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
// CHECK:     drv i32$ %x.data, %0, %1
// CHECK:     drv i1$ %x.valid, %2, %3
// CHECK:     drv i1$ %x.ready, %4, %5
// CHECK: }

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) {
// CHECK:     inst @fee.param3 () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready)
// CHECK: }
