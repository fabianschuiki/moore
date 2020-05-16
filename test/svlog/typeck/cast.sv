// RUN: moore %s -e foo -Vtypes

module foo;
    bit b;
    bit [7:0] v;
    bit [7:0][3:0] m;
    struct { bit x; bit [13:0] y; } s;
    struct { bit [13:0] x; bit y; } s2;

    // Cast to boolean

    assign b = !b;
    assign b = !v;
    assign b = !m;
    assign b = !s;
    // CHECK: 12: cast_chain(b) = bit
    // CHECK: 13: cast_chain(v) = bit [7:0] -> Bool bit
    // CHECK: 14: cast_chain(m) = bit [3:0] [7:0] -> SimpleBitVector logic [31:0] -> Bool bit
    // CHECK: 15: cast_chain(s) = struct -> SimpleBitVector logic [14:0] -> Bool bit

    assign b = v && b;
    assign b = v || b;
    assign b = v;
    // CHECK: 21: cast_chain(v) = bit [7:0] -> Bool bit
    // CHECK: 22: cast_chain(v) = bit [7:0] -> Bool bit
    // CHECK: 23: cast_chain(v) = bit [7:0] -> Range([0:0], false) bit [0:0] -> Transmute bit

    assign s = v;
    assign s = s2;
    // CHECK: 28: cast_chain(v) = bit [7:0] -> Range([14:0], false) bit [14:0] -> Domain(FourValued) logic [14:0] -> Struct struct
    // CHECK: 29: cast_chain(s2) = struct -> SimpleBitVector logic [14:0] -> Struct struct

endmodule
