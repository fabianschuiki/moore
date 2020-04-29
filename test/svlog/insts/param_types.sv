// RUN: moore %s -e A0 -e B -e C0

// Type parameter overrides

module A0;
    int t1;
    bit t2;
    A1 #(int) d1(t1);
    A1 #(bit) d2(t2);
endmodule

module A1 #(type T) (input T t);
endmodule

// CHECK: entity @A1.param1 (i32$ %t) -> () {
// CHECK: }
// CHECK:
// CHECK: entity @A1.param2 (i1$ %t) -> () {
// CHECK: }
// CHECK:
// CHECK: entity @A0 () -> () {
// CHECK:     inst @A1.param1 (i32$ %3) -> ()
// CHECK:     inst @A1.param2 (i1$ %6) -> ()
// CHECK: }


// Default type parameter types

module B #(type T = bit) (input T t);
endmodule

// CHECK: entity @B (i1$ %t) -> () {
// CHECK: }


// Dependencies between type parameters

module C0;
    int x1;
    bit x2;
    C1 #(bit) g1(x2, x2);
    C1 #(int) g2(x1, x1);
    C1 #(int, bit) g3(x1, x2);
endmodule

module C1 #(type T, type R = T) (input T t, input R r);
endmodule

// CHECK: entity @C1.param3 (i1$ %t, i1$ %r) -> () {
// CHECK: }
// CHECK:
// CHECK: entity @C1.param4 (i32$ %t, i32$ %r) -> () {
// CHECK: }
// CHECK:
// CHECK: entity @C1.param5 (i32$ %t, i1$ %r) -> () {
// CHECK: }
// CHECK:
// CHECK: entity @C0 () -> () {
// CHECK: }
