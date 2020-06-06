// RUN: moore %s -e lfsr_16bit_tb lfsr_16bit.sv -O0

module lfsr_16bit_tb;

    logic        clk_i;
    logic        rst_ni = 1'b1;
    logic        en_i;
    logic [15:0] out_o;

    lfsr_16bit #(.SEED(1)) dut (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .en_i(en_i),
        .out_o(out_o)
    );

    initial begin
        rst_ni <= #1ns 0;
        rst_ni <= #2ns 1;
        #4ns;
        en_i <= 1;
        repeat (10000000) begin
            clk_i <= #1ns 1;
            clk_i <= #2ns 0;
            #2ns;
        end
    end

endmodule
