// RUN: moore -e foo --format=mlir-native %s | FileCheck %s

// CHECK-LABEL: func @VoidFunc() {
// CHECK-NEXT:    return
// CHECK-NEXT:  }
function void VoidFunc;
endfunction

// CHECK-LABEL: func @RetOnlyFunc() -> i32 {
// CHECK-NEXT:    [[TMP:%.+]] = hw.constant 42 :
// CHECK-NEXT:    return [[TMP]]
// CHECK-NEXT:  }
function int RetOnlyFunc;
    return 42;
endfunction

module foo;
    initial begin
        int z;
        VoidFunc();
        z = RetOnlyFunc();
    end
endmodule

// CHECK-LABEL: llhd.proc @foo.initial
// CHECK: call @VoidFunc() : () -> ()
// CHECK: call @RetOnlyFunc() : () -> i32

