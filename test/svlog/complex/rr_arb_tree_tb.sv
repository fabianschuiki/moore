// RUN: moore %s -e rr_arb_tree_tb rr_arb_tree.sv -O0

module rr_arb_tree_tb;

  localparam NumIn = 8;
  localparam DataWidth = 32;

  logic                            clk_i;
  logic                            rst_ni = 1'b1;
  logic                            flush_i;
  logic [$clog2(NumIn)-1:0]        rr_i;
  logic [NumIn-1:0]                req_i;
  logic [NumIn-1:0]                gnt_o;
  logic [NumIn-1:0][DataWidth-1:0] data_i;
  logic                            gnt_i;
  logic                            req_o;
  logic [DataWidth-1:0]            data_o;
  logic [$clog2(NumIn)-1:0]        idx_o;

  rr_arb_tree #(
    .NumIn(NumIn),
    .DataWidth(DataWidth)
  ) dut (
    .clk_i,
    .rst_ni,
    .flush_i,
    .rr_i,
    .req_i,
    .gnt_o,
    .data_i,
    .gnt_i,
    .req_o,
    .data_o,
    .idx_o
  );

  assign req_i = -1;
  assign gnt_i = req_o;

  initial begin
    rst_ni <= #1ns 0;
    rst_ni <= #2ns 1;
    #4ns;
    repeat (5000000) begin
      clk_i <= #1ns 1;
      clk_i <= #2ns 0;
      #2ns;
    end
  end

endmodule
