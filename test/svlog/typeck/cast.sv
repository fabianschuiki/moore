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
    // CHECK: 12: cast_chain(b) = bit -> PackSBVT bit [0:0] -> Bool logic
    // CHECK: 13: cast_chain(v) = bit [7:0] -> Bool logic
    // CHECK: 14: cast_chain(m) = bit [3:0][7:0] -> PackSBVT bit [31:0] -> Bool logic
    // CHECK: 15: cast_chain(s) = struct packed { bit x; bit [13:0] y; } -> PackSBVT bit [14:0] -> Bool logic

    assign b = v && b;
    assign b = v || b;
    assign b = v;
    // CHECK: 21: cast_chain(v) = bit [7:0] -> Bool logic
    // CHECK: 22: cast_chain(v) = bit [7:0] -> Bool logic
    // CHECK: 23: cast_chain(v) = bit [7:0] -> Range([0:0], false) bit [0:0] -> UnpackSBVT bit

    assign s = v;
    assign s = s2;
    // CHECK: 28: cast_chain(v) = bit [7:0] -> Range([14:0], false) bit [14:0] -> UnpackSBVT struct packed { bit x; bit [13:0] y; }
    // CHECK: 29: cast_chain(s2) = struct packed { bit [13:0] x; bit y; } -> PackSBVT bit [14:0] -> UnpackSBVT struct packed { bit x; bit [13:0] y; }

    // Operation type casts

    bit [5:0] a1;
    bit [6:0] b1;

    assign b = a1 == b1;
    assign b = a1 != b1;
    assign b = a1 > b1;
    assign b = a1 >= b1;
    assign b = a1 < b1;
    assign b = a1 <= b1;

endmodule
