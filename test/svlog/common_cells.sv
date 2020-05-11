// RUN: moore %s -e foo -I ../third-party/common_cells/include ../third-party/common_cells/src/*.sv

module foo;
    typedef int unsigned addr_t;
    typedef struct packed {
      int unsigned idx;
      addr_t start_addr;
      addr_t end_addr;
    } rule_t;

    addr_decode #(.NoIndices(4), .NoRules(4), .addr_t(addr_t), .rule_t(rule_t)) i0 ();
    // cb_filter i0 ();
    cdc_2phase #(.T(logic [41:0])) i0 ();
    cdc_fifo_2phase #(.T(logic [41:0])) i0 ();
    rr_arb_tree #(.NumIn(4)) i0 ();
    // stream_arbiter_flushable #(.N_INP(4)) i0 ();
    stream_delay i0 ();
    stream_demux #(.N_OUP(4)) i0 ();
    // sub_per_hash i0 ();
endmodule
