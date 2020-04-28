// RUN: moore %s -e test -Vports
module test (
    input [7:0] a,
    input signed [7:0] b, c, d, // Multiple ports that share all
                                // attributes can be declared together.
    output [7:0] e,             // Every attribute of the declaration
                                // must be in the one declaration.
    output var signed [7:0] f, g,
    output signed [7:0] h
);
    // It is illegal to redeclare any ports of
    // the module in the body of the module.

    // CHECK: Ports of `test`:
    // CHECK: 0: input wire logic [7:0] a
    // -CHECK: 1: input wire logic signed [7:0] b
    // -CHECK: 2: input wire logic signed [7:0] c
    // -CHECK: 3: input wire logic signed [7:0] d
    // CHECK: 4: output wire logic [7:0] e
    // -CHECK: 5: output var logic signed [7:0] f
    // -CHECK: 6: output var logic signed [7:0] g
    // -CHECK: 7: output var logic signed [7:0] h
endmodule
