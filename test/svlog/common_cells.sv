// RUN: moore %s -e foo -I ../third-party/common_cells/include ../third-party/common_cells/src/*.sv

module foo;
    stream_demux #(.N_OUP(4)) i0 ();
endmodule
