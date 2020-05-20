// RUN: moore %s -e A
module A;
    B b();
endmodule

module B;
endmodule

// CHECK: entity @B.param1 () -> () {
// CHECK: }
// CHECK: entity @A () -> () {
// CHECK:     inst @B.param1 () -> ()
// CHECK: }
