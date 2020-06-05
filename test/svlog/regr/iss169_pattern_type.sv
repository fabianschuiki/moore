// RUN: moore %s -e foo -O0
module foo;
    typedef struct packed { int x; int y; } T;
    var x = T'{default: 0};
    // CHECK: %x = sig {i32, i32} %2
endmodule
