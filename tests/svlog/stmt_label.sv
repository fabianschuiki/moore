package empty_package;
    function void test ();
    endfunction : test
endpackage : empty_package

module stmt_label;
    full_write : assert property (
        @(posedge clk_i) disable iff (~rst_ni) (full_o |-> ~push_i))
        else $fatal (1, "Trying to push new data although the FIFO is full.");
endmodule : stmt_label
