// RUN: moore %s -e foo -I ../third-party/common_cells/include ../third-party/common_cells/src/*.sv

module foo;
    typedef int unsigned addr_t;
    typedef struct packed {
      int unsigned idx;
      addr_t start_addr;
      addr_t end_addr;
    } rule_t;

    addr_decode #(.NoIndices(4), .NoRules(4), .addr_t(addr_t), .rule_t(rule_t)) i0();
    // cb_filter i0();
    cdc_2phase #(.T(logic [41:0])) i0();
    cdc_fifo_2phase #(.T(logic [41:0])) i0();
    cdc_fifo_gray #(.T(logic [41:0])) i0();
    clk_div i0();
    counter i0();
    delta_counter i0();
    // ecc_decode i0();
    // ecc_encode i0();
    // edge_detect i0(); // broken in repo
    // edge_propagator_rx i0(); // broken in repo
    // edge_propagator i0(); // broken in repo
    edge_propagator_tx i0();
    exp_backoff i0();
    // fall_through_register i0(); // broken in repo
    fifo_v3 i0();
    binary_to_gray #(.N(9)) i0();
    gray_to_binary #(.N(9)) i0();
    // id_queue #(.ID_WIDTH(2), .CAPACITY(3), .data_t(logic [41:0])) i0();
    lfsr_16bit i0();
    lfsr_8bit i0();
    // lfsr i0();
    lzc i0();
    max_counter i0();
    mv_filter i0();
    onehot_to_bin i0();
    // plru_tree i0();
    popcount #(.INPUT_WIDTH(16)) i0();
    rr_arb_tree #(.NumIn(4)) i0();
    rstgen_bypass i0();
    rstgen i0();
    serial_deglitch i0();
    shift_reg #(.Depth(0)) i0();
    shift_reg #(.Depth(1)) i0();
    shift_reg #(.Depth(4)) i0();
    spill_register i0();
    sram #(.NUM_WORDS(16)) i0();
    // stream_arbiter_flushable #(.N_INP(4)) i0();
    // stream_arbiter #(.N_INP(4)) i0();
    stream_delay i0();
    stream_demux #(.N_OUP(4)) i0();
    stream_fifo i0();
    stream_filter i0();
    stream_fork_dynamic #(.N_OUP(4)) i0();
    stream_fork #(.N_OUP(4)) i0();
    stream_join #(.N_INP(4)) i0();
    stream_mux #(.N_INP(4)) i0();
    // stream_register i0(); // broken in repo
    // sub_per_hash i0();
    sync i0();
    // sync_wedge i0(); // broken in repo
    unread i0();
endmodule
