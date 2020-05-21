// RUN: moore %s
module foo;
    int foo [];       // unsized_dimension
    int foo [4];      // unpacked_dimension
    int foo [4:0];    // unpacked_dimension
    int foo [string]; // associative_dimension
    int foo [*];      // associative_dimension
    int foo [$];      // queue_dimension
    int foo [$:4];    // queue_dimension
endmodule
