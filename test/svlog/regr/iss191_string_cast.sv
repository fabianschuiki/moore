// RUN: moore %s -e foo -O0

module foo;
    reg [79:0] x;
    assign x = "Hello, World!";
endmodule
