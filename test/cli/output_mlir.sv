// RUN: moore %s -e foo --format mlir

module foo (output int x);
    initial x = 42;
endmodule

// CHECK: llhd.proc @foo.initial.15.0() -> (%x: !llhd.sig<i32> ) {
// CHECK:     br ^0
// CHECK: ^0:
// CHECK:     %1 = llhd.const 42 : i32
// CHECK:     %2 = llhd.const #llhd.time<0s, 0d, 1e> : !llhd.time
// CHECK:     llhd.drv %x, %1 after %2 : !llhd.sig<i32>
// CHECK:     llhd.halt
// CHECK: }
// CHECK:
// CHECK: llhd.entity @foo() -> (%x: !llhd.sig<i32> ) {
// CHECK:     llhd.inst "inst" @foo.initial.15.0() -> (%x) : () -> (!llhd.sig<i32>)
// CHECK: }
