// RUN: moore %s -e foo -I ../third-party/common_cells/include ../third-party/common_cells/src/*.sv

module foo;
    typedef int unsigned addr_t;
    typedef struct packed {
      int unsigned idx;
      addr_t start_addr;
      addr_t end_addr;
    } rule_t;

    addr_decode #(.NoIndices(4), .NoRules(4), .addr_t(addr_t), .rule_t(rule_t)) i0();
    // cb_filter i1();
    cdc_2phase #(.T(logic [41:0])) i2();
    cdc_fifo_2phase #(.T(logic [41:0])) i3();
    cdc_fifo_gray #(.T(logic [41:0])) i4();
    clk_div i5();
    counter i6();
    delta_counter i7();
    // ecc_decode i8();
    // ecc_encode i9();
    // edge_detect i10(); // broken in repo
    // edge_propagator_rx i11(); // broken in repo
    // edge_propagator i12(); // broken in repo
    edge_propagator_tx i13();
    exp_backoff i14();
    // fall_through_register i15(); // broken in repo
    fifo_v3 i16();
    binary_to_gray #(.N(9)) i17();
    gray_to_binary #(.N(9)) i18();
    // id_queue #(.ID_WIDTH(2), .CAPACITY(3), .data_t(logic [41:0])) i19();
    lfsr_16bit i20();
    lfsr_8bit i21();
    lfsr i22();
    lzc i23();
    max_counter i24();
    mv_filter i25();
    onehot_to_bin i26();
    // plru_tree i27();
    popcount #(.INPUT_WIDTH(16)) i28();
    rr_arb_tree #(.NumIn(4)) i29();
    rstgen_bypass i30();
    rstgen i31();
    serial_deglitch i32();
    shift_reg #(.Depth(0)) i33();
    shift_reg #(.Depth(1)) i34();
    shift_reg #(.Depth(4)) i35();
    spill_register i36();
    sram #(.NUM_WORDS(16)) i37();
    // stream_arbiter_flushable #(.N_INP(4)) i38();
    // stream_arbiter #(.N_INP(4)) i39();
    stream_delay i40();
    stream_demux #(.N_OUP(4)) i41();
    stream_fifo i42();
    stream_filter i43();
    stream_fork_dynamic #(.N_OUP(4)) i44();
    stream_fork #(.N_OUP(4)) i45();
    stream_join #(.N_INP(4)) i46();
    stream_mux #(.N_INP(4)) i47();
    // stream_register i48(); // broken in repo
    // sub_per_hash i49();
    sync i50();
    // sync_wedge i51(); // broken in repo
    unread i52();
endmodule
