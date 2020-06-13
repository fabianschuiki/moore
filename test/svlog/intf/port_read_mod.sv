// RUN: moore %s -e foo -O0

module foo (bar x, bar y[1][1:0]);
	logic z0, z1, z2;
	assign z0 = x.valid & x.ready | !x.data;
    assign z1 = y[0][0].valid & y[0][0].ready | !y[0][0].data;
    assign z2 = y[0][1].valid & y[0][1].ready | !y[0][1].data;
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;
endinterface

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready, [1 x [2 x i32]]$ %y.data, [1 x [2 x i1]]$ %y.valid, [1 x [2 x i1]]$ %y.ready) {
// CHECK:     %3 = and i1 %x.valid.prb, %x.ready.prb
// CHECK:     %5 = neq i32 %x.data.prb, %4
// CHECK: }
