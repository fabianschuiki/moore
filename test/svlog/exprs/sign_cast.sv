// RUN: moore %s -e foo
// IGNORE  see issue #138

module foo;
    int x;
    int y = unsigned'(x);
    int z = signed'(x);
endmodule
