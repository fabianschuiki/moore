// RUN: moore %s -e foo
// IGNORE  see issue #132

module foo (
    output bit x = 0,
    output bit y = 1
);
    // CHECK: entity @foo () -> (i1$ %x, i1$ %y) {
    // CHECK:     %0 = const i1 0
    // CHECK:     %2 = const i1 1
    // CHECK: }
endmodule
