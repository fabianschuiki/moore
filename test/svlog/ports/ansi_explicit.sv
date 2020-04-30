// RUN: moore %s -e foo -Vports

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

    // CHECK: Ports of `foo`:
    // CHECK:   internal:
    // CHECK:     0: input wire logic foo
    // CHECK:     1: input wire logic [7:0] bar
    // CHECK:     2: input wire logic [41:0] [7:0] baz
    // CHECK:   external:
    // CHECK:     0: .a()
    // CHECK:     1: .b(foo)
    // CHECK:     2: .c(bar[..])
    // CHECK:     3: .d(baz[..][..])
    // CHECK:     4: .e(bar)
    // CHECK:     5: .f({bar, bar})
    // CHECK:     6: .g({bar[..], baz[..][..]})

    // CHECK: entity @foo (i1$ %foo, i8$ %bar, [8 x i42]$ %baz) -> () {
endmodule
