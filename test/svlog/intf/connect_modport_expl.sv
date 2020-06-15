// RUN: moore %s -e foo -O0

module foo (bar.in x, bar.out y);
    fee u0(x, y);
endmodule

module fee (bar.in x, bar.out y);
    assign y.data = x.data;
    assign y.valid = x.valid;
    assign x.ready = y.ready;
endmodule

interface bar;
    logic [31:0] data;
    logic valid;
    logic ready;

    modport in (input data, valid, output ready);
    modport out (output data, valid, input ready);
endinterface

// CHECK: entity @fee.param2 (i32$ %x.data, i1$ %x.valid, i1$ %y.ready) -> (i1$ %x.ready, i32$ %y.data, i1$ %y.valid) {
// CHECK:     drv i32$ %y.data, %x.data.prb, %0
// CHECK:     drv i1$ %y.valid, %x.valid.prb, %1
// CHECK:     drv i1$ %x.ready, %y.ready.prb, %2
// CHECK: }

// CHECK: entity @foo (i32$ %x.data, i1$ %x.valid, i1$ %y.ready) -> (i1$ %x.ready, i32$ %y.data, i1$ %y.valid) {
// CHECK:     inst @fee.param2 (i32$ %1, i1$ %4, i1$ %7) -> (i1$ %x.ready, i32$ %y.data, i1$ %y.valid)
// CHECK: }
