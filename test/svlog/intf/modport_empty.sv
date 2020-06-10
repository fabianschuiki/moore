// RUN: moore %s -e foo -O0

module foo (bar.in x, bar.out y);
endmodule

interface bar;
    modport in ();
    modport out ();
endinterface

// CHECK: entity @foo () -> () {
// CHECK: }
