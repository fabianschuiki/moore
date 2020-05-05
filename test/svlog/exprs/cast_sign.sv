// RUN: moore %s -e foo -Vtypes

module foo;
    int signed x;
    bit unsigned y;
    initial begin
        unsigned'(x);
        unsigned'(y);
        signed'(x);
        signed'(y);
    end
    // CHECK: 7: type(unsigned'(x)) = int unsigned
    // CHECK: 8: type(unsigned'(y)) = bit
    // CHECK: 9: type(signed'(x)) = int
    // CHECK: 10: type(signed'(y)) = bit signed
endmodule
