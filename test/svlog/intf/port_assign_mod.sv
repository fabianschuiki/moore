// RUN: moore %s -e foo -O0

module foo (bar x, bar y[1][1:0]);
    assign x.data = 42;
    assign x.valid = 1;
    assign x.ready = 0;
    assign y[0][0].data = 9001;
    assign y[0][0].valid = 1;
    assign y[0][0].ready = 0;
    assign y[0][1].data = 1337;
    assign y[0][1].valid = 1;
    assign y[0][1].ready = 0;
endmodule

interface bar;
    logic [31:0] data;
    logic valid;
    logic ready;
endinterface

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready, [1 x [2 x i32]]$ %y.data, [1 x [2 x i1]]$ %y.valid, [1 x [2 x i1]]$ %y.ready) {
// CHECK:     drv i32$ %x.data, %1, %0
// CHECK:     drv i1$ %x.valid, %3, %2
// CHECK:     drv i1$ %x.ready, %5, %4
// CHECK: }
