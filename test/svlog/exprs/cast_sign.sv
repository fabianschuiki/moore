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
    // CHECK: 7: cast_type(unsigned'(x)) = int unsigned
    // CHECK: 8: cast_type(unsigned'(y)) = bit
    // CHECK: 9: cast_type(signed'(x)) = int
    // CHECK: 10: cast_type(signed'(y)) = bit signed
endmodule
