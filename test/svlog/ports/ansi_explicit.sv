// RUN: moore %s -e foo
// IGNORE
module foo (
    input .a(),
    input .b(foo),
    input .c(bar[7:0]),
    input .d(baz[7:0][41:0]),
    input .e({bar}),
    input .f({bar, bar}),
    input .g({bar[7:0], baz[7:0][41:0]})
);
    logic foo;
    logic [7:0] bar;
    logic [7:0][41:0] baz;
endmodule
