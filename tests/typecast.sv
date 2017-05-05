module A1 (input logic [63:0] a);

    typedef struct packed {
        logic [3:0]  mode;
        logic [15:0] asid;
        logic [43:0] ppn;
    } sapt_t;

    sapt_t b;
    assign b = sapt_t'(a);

endmodule