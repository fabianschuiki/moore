// RUN: moore %s -e foo

module foo;
    logic [7:0] a;
    logic [3:0] b;
    initial begin
        {a} = 8'd42;
        {a, b} = 12'd42;
        {a[1:0], b[1:0]} = 4'hA;
    end
endmodule
