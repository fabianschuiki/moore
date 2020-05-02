// RUN: moore %s -e foo
// IGNORE  see issue #139

module foo;
    int x, y;
    assert final (x == y);
endmodule
