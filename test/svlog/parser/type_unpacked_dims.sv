// RUN: moore %s
module foo;
    int foo1 [];       // unsized_dimension
    int foo2 [4];      // unpacked_dimension
    int foo3 [4:0];    // unpacked_dimension
    int foo4 [string]; // associative_dimension
    int foo5 [*];      // associative_dimension
    int foo6 [$];      // queue_dimension
    int foo7 [$:4];    // queue_dimension
endmodule
