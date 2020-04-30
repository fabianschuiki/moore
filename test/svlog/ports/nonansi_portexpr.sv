// RUN: moore %s -e foo

module foo (
    bar[7:0],
    baz[7:0][41:0],
    {bar},
    {bar, bar},
    {bar[7:0], baz[7:0][41:0]},
    .a(),
    .b(foo),
    .c(bar[7:0]),
    .d(baz[7:0][41:0]),
    .e({bar}),
    .f({bar, bar}),
    .g({bar[7:0], baz[7:0][41:0]})
);

    input foo;
    input [7:0] bar;
    input [7:0][41:0] baz;

    // CHECK: entity @foo (i1$ %foo, i8$ %bar, [8 x i42]$ %baz) -> () {
endmodule
