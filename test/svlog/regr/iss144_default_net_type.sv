// RUN: moore %s -e foo

module foo;
    wire                a0;
    wire [7:0]          a1;
    wire unsigned       a2;
    wire signed         a3;
    wire unsigned [7:0] a4;
    wire signed [7:0]   a5;

    wire    b00;
    wand    b01;
    wor     b02;
    tri     b03;
    triand  b04;
    trior   b05;
    tri0    b06;
    tri1    b07;
    trireg  b08;
    supply0 b09;
    supply1 b10;
    uwire   b11;
endmodule
