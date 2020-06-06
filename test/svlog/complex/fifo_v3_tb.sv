// RUN: moore %s -e fifo_v3_tb fifo_v3.sv -O0

module fifo_v3_tb;

    logic clk_i;
    logic rst_ni = 1'b1;
    logic full_o;
    logic empty_o;
    int   data_i;
    logic push_i;
    int   data_o;
    logic pop_i;

    fifo_v3 #(.dtype(int), .DEPTH(16)) dut (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .flush_i(1'b0),
        .testmode_i(1'b0),
        .full_o(full_o),
        .empty_o(empty_o),
        .data_i(data_i),
        .push_i(push_i),
        .data_o(data_o),
        .pop_i(pop_i)
    );

    initial begin
        rst_ni <= #1ns 0;
        rst_ni <= #2ns 1;
        #4ns;
        repeat (1000000) begin
            clk_i <= #1ns 1;
            clk_i <= #2ns 0;
            #2ns;
        end
    end

    always_comb push_i <= #0.25ns !full_o;
    always @(posedge clk_i iff !full_o) data_i <= #0.25ns data_i + 1;

    always_comb pop_i <= #0.25ns !empty_o;

endmodule
