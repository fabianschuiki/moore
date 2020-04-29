// RUN: moore %s -e A
module A;
    B b();
endmodule

module B;
endmodule

// CHECK: entity @B () -> () {
// CHECK: }
// CHECK: entity @A () -> () {
// CHECK:     inst @B () -> ()
// CHECK: }
