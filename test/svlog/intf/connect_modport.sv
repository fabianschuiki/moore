// RUN: moore %s -e foo -O0

module foo (bar.in x, bar.out y);
	fee u0(x, y);
endmodule

module fee (bar.in x, bar.out y);
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;

    modport in (input data, valid, output ready);
    modport out (output data, valid, input ready);
endinterface

// CHECK: entity @fee (i32$ %x.data, i1$ %x.valid, i1$ %y.ready) -> (i1$ %x.ready, i32$ %y.data, i1$ %y.valid) {
// CHECK: }

// CHECK: entity @foo (i32$ %x.data, i1$ %x.valid, i1$ %y.ready) -> (i1$ %x.ready, i32$ %y.data, i1$ %y.valid) {
// CHECK: }
