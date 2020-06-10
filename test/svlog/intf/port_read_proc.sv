// RUN: moore %s -e foo -O0

module foo (bar x);
  logic z;
  initial begin
    z = x.valid & x.ready | !x.data;
  end
endmodule

interface bar;
  logic [31:0] data;
  logic valid;
  logic ready;
endinterface

// CHECK: proc %foo.initial.41.0 (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) -> (i1$ %z) {
// CHECK:     %1 = and i1 %x.valid1, %x.ready1
// CHECK:     %3 = neq i32 %x.data1, %2
// CHECK: }

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) {
// CHECK:     %z = sig i1 %0
// CHECK:     inst %foo.initial.41.0 (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) -> (i1$ %z)
// CHECK: }
