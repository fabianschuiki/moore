// RUN: moore %s -e foo

module foo;
    bit reset;
    default disable iff (!reset);
endmodule
