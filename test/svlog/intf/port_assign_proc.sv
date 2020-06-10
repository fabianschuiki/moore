// RUN: moore %s -e foo -O0

module foo (bar x);
  initial begin
    x.data = 42;
    x.valid = 1;
    x.ready = 0;
  end
endmodule

interface bar;
  logic [31:0] data;
  logic valid;
  logic ready;
endinterface

// CHECK: proc %foo.initial.60.0 () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) {
// CHECK:     drv i32$ %x.data, %1, %2
// CHECK:     drv i1$ %x.valid, %3, %4
// CHECK:     drv i1$ %x.ready, %5, %6
// CHECK: }

// CHECK: entity @foo () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready) {
// CHECK:     inst %foo.initial.60.0 () -> (i32$ %x.data, i1$ %x.valid, i1$ %x.ready)
// CHECK: }
