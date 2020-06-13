// RUN: moore %s -e foo -O0

module foo;
    bar x();
    bar y[3:0]();
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
// CHECK:     %y.data = sig [4 x i32] %7
// CHECK:     %y.valid = sig [4 x i1] %12
// CHECK:     %y.ready = sig [4 x i1] %17
// CHECK: }
