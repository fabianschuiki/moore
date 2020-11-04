// RUN: moore %s -e foo

function int bar;
    return 42;
endfunction

module foo (output int z);
    initial z = bar();
endmodule
