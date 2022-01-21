// RUN: moore -e foo --format=mlir-native %s | FileCheck %s

function void bar;
endfunction

module foo;
    initial bar();
endmodule

// CHECK:      llhd.proc @foo.initial
// CHECK-NEXT:   call @bar()

// CHECK:      func @bar() {
// CHECK-NEXT:     return
// CHECK-NEXT: }
