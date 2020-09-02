// RUN: moore %s -e foo

function int bar(int a, int b);
    return a + b;
endfunction

module foo (output int z);
    assign z = bar(20, 22);
endmodule
