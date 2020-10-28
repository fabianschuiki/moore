// RUN: moore %s -e foo -O0

module foo;
	bar x();
	logic z;
	assign z = x.valid & x.ready | !x.data;
endmodule

interface bar;
	logic [31:0] data;
	logic valid;
	logic ready;
endinterface

// CHECK: entity @foo () -> () {
// CHECK:     %x.data = sig i32 %1
// CHECK:     %x.valid = sig i1 %2
// CHECK:     %x.ready = sig i1 %3
// CHECK:     %5 = and i1 %x.valid.prb, %x.ready.prb
// CHECK:     %7 = neq i32 %x.data.prb, %6
// CHECK: }
