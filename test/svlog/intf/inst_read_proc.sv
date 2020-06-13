// RUN: moore %s -e foo -O0

module foo;
  bar x();
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

// CHECK: proc %foo.initial.42.0 (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) -> (i1$ %z) {
// CHECK:     %1 = and i1 %x.valid.prb, %x.ready.prb
// CHECK:     %3 = neq i32 %x.data.prb, %2
// CHECK: }

// CHECK: entity @foo () -> () {
// CHECK:     %z = sig i1 %0
// CHECK:     %x.data = sig i32 %1
// CHECK:     %x.valid = sig i1 %2
// CHECK:     %x.ready = sig i1 %3
// CHECK:     inst %foo.initial.42.0 (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) -> (i1$ %z)
// CHECK: }
