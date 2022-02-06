// RUN: moore -e foo --format=mlir-native %s | FileCheck %s

function void VoidFunc;
endfunction

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
// CHECK: [[RETVAL:%.+]] = call @RetOnlyFunc() : () -> (i32)

// CHECK-LABEL: func @VoidFunc() {
// CHECK-NEXT:    return
// CHECK-NEXT:  }

// CHECK-LABEL: func @RetOnlyFunc() {
// CHECK-NEXT:    return
// CHECK-NEXT:  }

