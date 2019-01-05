// @elab A
// Make sure the compiler does not complain about the "int" in the next line.
module A #(parameter int N = 8);
endmodule

// @elab B
module B #(parameter type T = int);
endmodule
