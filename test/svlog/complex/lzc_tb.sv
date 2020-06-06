// RUN: moore %s -e lzc_tb lzc.sv lfsr_16bit.sv -O0

module lzc_tb;

  localparam WIDTH = 16;

  logic [WIDTH-1:0] in_i;
  logic [$clog2(WIDTH)-1:0] cnt_o;
  logic empty_o;

  lzc #(.WIDTH(WIDTH), .MODE(1)) dut (
    .in_i(in_i),
    .cnt_o(cnt_o),
    .empty_o(empty_o)
  );

  logic clk_i;
  logic rst_ni = 1'b1;

  lfsr_16bit #(.SEED(1)) i_lfsr (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      .en_i(1'b1),
      .out_o(in_i)
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

endmodule
