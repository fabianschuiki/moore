// RUN: moore %s -e foo -O0

module foo;
    genvar i;
    for (i = 1; i < 4; i = i + 1) begin
        int x = i;
    end
    for (i = 11; i < 14; i += 1) begin
        int y = i;
    end
    for (i = 21; i < 24; i++) begin
        int z = i;
    end
endmodule
