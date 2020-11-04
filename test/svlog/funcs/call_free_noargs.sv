// RUN: moore %s -e foo
// IGNORE  part of #168

function int bar;
    return 42;
endfunction

module foo (output int z);
    initial z = bar();
endmodule
