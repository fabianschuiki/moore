// RUN: moore %s -e foo -O0

module foo;
    genvar i;
    for (i = 1; i < 4; i++) begin
    end
endmodule
