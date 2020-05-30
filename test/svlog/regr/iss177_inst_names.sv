// RUN: moore %s
// Instances should emit a definition.

module foo;
    bar u0();
    bar u1();

    int z = u0.x + u1.x;
endmodule

module bar;
    int x = 42;
endmodule
