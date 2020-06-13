// RUN: moore %s -e foo -O0

module foo (bar x, bar y[1][1:0]);
    initial begin
        x.data = 42;
        x.valid = 1;
        x.ready = 0;
        y[0][0].data = 9001;
        y[0][0].valid = 1;
        y[0][0].ready = 0;
        y[0][1].data = 1337;
        y[0][1].valid = 1;
        y[0][1].ready = 0;
    end
endmodule

interface bar;
    logic [31:0] data;
    logic valid;
    logic ready;
endinterface

// CHECK: proc %foo.initial.260.0 () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready, [1 x [2 x i32]]$ %y.data, [1 x [2 x i1]]$ %y.valid, [1 x [2 x i1]]$ %y.ready) {
// CHECK:     drv i32$ %x.data, %1, %2
// CHECK:     drv i1$ %x.valid, %3, %4
// CHECK:     drv i1$ %x.ready, %5, %6
// CHECK: }

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready, [1 x [2 x i32]]$ %y.data, [1 x [2 x i1]]$ %y.valid, [1 x [2 x i1]]$ %y.ready) {
// CHECK:     inst %foo.initial.260.0 () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready, [1 x [2 x i32]]$ %y.data, [1 x [2 x i1]]$ %y.valid, [1 x [2 x i1]]$ %y.ready)
// CHECK: }
