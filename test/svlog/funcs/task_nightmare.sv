// RUN: moore %s -e foo
// IGNORE

module foo;
    bar b();
    initial b.magic();
endmodule

module bar;
    task magic;
    endtask
endmodule
