// RUN: moore %s -e foo -Vinsts

module foo;
    bar #(4) a0 (42);
endmodule

module bar #(parameter bit [4:0] X)(input bit [19:0] a);
endmodule
