// RUN: moore %s -e foo
// IGNORE  see issue #140

module foo;
    bit reset;
    default disable iff (!reset);
endmodule
