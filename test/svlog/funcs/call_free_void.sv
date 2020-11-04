// RUN: moore %s -e foo
// IGNORE  part of #168

function void bar;
endfunction

module foo;
    initial bar();
endmodule
