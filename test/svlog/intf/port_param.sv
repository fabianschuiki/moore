// RUN: moore %s -e foo -O0

module foo;
    bar #(32, logic) x();
    bar #(19, byte) y();

    fee u0(x);
    fee u1(y);
endmodule

module fee (bar.in z);
    int wd = $bits(z.data);
    int wv = $bits(z.valid);

    initial begin
        int wd = $bits(z.data);
        int wv = $bits(z.valid);
    end
endmodule

interface bar #(
    parameter int N,
    parameter type T
);
    logic [N-1:0] data;
    T valid;
    logic ready;

    modport in (input data, valid, output ready);
    modport out (output data, valid, input ready);
endinterface

// CHECK: entity @fee.param7 (i32$ %z.data, i1$ %z.valid) -> (i1$ %z.ready) {
// CHECK: }
// CHECK: entity @fee.param8 (i19$ %z.data, i8$ %z.valid) -> (i1$ %z.ready) {
// CHECK: }
// CHECK: entity @foo () -> () {
// CHECK: }
