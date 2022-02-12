// RUN: moore -e foo --format=mlir-native %s | FileCheck %s

// CHECK-LABEL: func @ShiftExpressions(%arg0: i22, %arg1: i6) {
function void ShiftExpressions(bit signed [21:0] x, bit [5:0] y);
    // CHECK: moore.mir.shl %{{.+}}, %{{.+}} : !moore.packed<range<bit, 21:0>>, !moore.packed<range<bit, 5:0>>
    // CHECK: moore.mir.shl arithmetic %{{.+}}, %{{.+}} : !moore.packed<range<bit, 21:0>>, !moore.packed<range<bit, 5:0>>
    bit [21:0] a = x << y;
    bit signed [21:0] b = x <<< y;

    // CHECK: moore.mir.shr %{{.+}}, %{{.+}} : !moore.packed<range<bit, 21:0>>, !moore.packed<range<bit, 5:0>>
    // CHECK: moore.mir.shr arithmetic %{{.+}}, %{{.+}} : !moore.packed<range<bit, 21:0>>, !moore.packed<range<bit, 5:0>>
    bit [21:0] c = x >> y;
    bit signed [21:0] d = x >>> y;
endfunction

// CHECK-LABEL: func @Concat(
// CHECK-SAME: [[X:%.+]]: i4, [[Y:%.+]]: i2, [[Z:%.+]]: i1) -> i7 {
function bit [6:0] Concat(bit [3:0] x, bit [1:0] y, bit z);
    // CHECK-NEXT: [[TMP:%.+]] = moore.mir.concat [[X]], [[Y]], [[Z]]
    // CHECK-NEXT: return [[TMP]]
    return {x, y, z};
endfunction

module foo;
endmodule
