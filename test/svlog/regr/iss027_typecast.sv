// RUN: moore %s

module A1 (input logic [63:0] a);

    typedef struct packed {
        logic [3:0]  mode;
        logic [15:0] asid;
        logic [43:0] ppn;
    } sapt_t;

    // Cast from a signal (a port, in this case)
    sapt_t b;
    assign b = sapt_t'(a);

    // Cast from a literal
    int some_int;
    assign some_int = int'(7.0);

endmodule
