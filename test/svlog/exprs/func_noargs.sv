// RUN: moore %s -e foo

function int bar;
    return 42;
endfunction

module foo;
    initial begin
        int a;
        a = bar() + 42;
        bar();
    end
endmodule
