// RUN: moore %s -e same_input
// IGNORE

module same_input (a,a);
    input a; // This is legal. The inputs are tied together.
endmodule
