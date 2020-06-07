// RUN: moore %s -e foo -O0

module foo;
	bar x();
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
// CHECK: }
