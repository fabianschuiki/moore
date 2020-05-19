// RUN: moore %s -e foo

module foo;
    int a, b;
    initial if (a === b);
    initial if (a !== b);
endmodule
