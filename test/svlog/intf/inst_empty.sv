// RUN: moore %s -e foo -O0

module foo;
    bar x();
    bar y[3:0]();
endmodule

interface bar;
endinterface

// CHECK: entity @foo () -> () {
// CHECK: }
