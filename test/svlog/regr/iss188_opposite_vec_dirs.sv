// RUN: moore %s -e foo -O0

module foo (input logic [8:1] x, output logic [2:9] z);
    assign z = x;

    logic b0, b1, b2, b3;
    assign b0 = x[1];
    assign b1 = x[8];
    assign b2 = z[2];
    assign b3 = z[9];
endmodule
