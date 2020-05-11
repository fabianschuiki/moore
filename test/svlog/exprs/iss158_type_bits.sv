// RUN: moore %s -e foo
// IGNORE  see issue #158

module foo;
    parameter int a = 42;
    parameter type b = logic [41:0];
    int x0 = $bits(42);
    int x1 = $bits(logic [41:0]);
    int x2 = $bits(a);
    int x3 = $bits(b);
endmodule
