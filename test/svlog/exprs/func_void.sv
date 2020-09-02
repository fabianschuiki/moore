// RUN: moore %s -e foo

function void bar;
endfunction

module foo;
    initial bar();
endmodule
