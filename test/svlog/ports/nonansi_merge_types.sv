// RUN: moore %s -e foo
// IGNORE
module foo(a, b);
    input a;
    bit a;

    input b;
    wire bit b;
endmodule
