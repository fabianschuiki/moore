// RUN: moore %s -e cdc_2phase_tb cdc_2phase.sv -O0

module cdc_2phase_tb;

  localparam N = 500000;
  int ERRORS = 0;

  logic src_rst_ni = 1'b1;
  logic src_clk_i;
  int   src_data_i;
  logic src_valid_i;
  logic src_ready_o;

  logic dst_rst_ni = 1'b1;
  logic dst_clk_i;
  int   dst_data_o;
  logic dst_valid_o;
  logic dst_ready_i;

  cdc_2phase #(.T(int)) dut (
    .src_rst_ni(src_rst_ni),
    .src_clk_i(src_clk_i),
    .src_data_i(src_data_i),
    .src_valid_i(src_valid_i),
    .src_ready_o(src_ready_o),
    .dst_rst_ni(dst_rst_ni),
    .dst_clk_i(dst_clk_i),
    .dst_data_o(dst_data_o),
    .dst_valid_o(dst_valid_o),
    .dst_ready_i(dst_ready_i)
  );

  initial begin
    src_rst_ni = 0;
    #1ns;
    src_rst_ni = 1;
    #1ns;
    for (int i = 0; i < N; ++i) begin
      while (!src_ready_o) begin
        src_clk_i = 1;
        #1ns;
        src_clk_i = 0;
        #1ns;
      end
      src_clk_i = 1;
      src_data_i = i;
      src_valid_i = 1;
      #1ns;
      src_clk_i = 0;
      #1ns;
    end
  end

  initial begin
    dst_rst_ni = 0;
    #1ns;
    dst_rst_ni = 1;
    #1ns;
    dst_ready_i = 1;
    for (int i = 0; i < N; ++i) begin
      while (!dst_valid_o) begin
        dst_clk_i = 1;
        #1ns;
        dst_clk_i = 0;
        #1ns;
      end
      dst_clk_i = 1;
      assert(i == dst_data_o);
      ERRORS += (i != dst_data_o);
      #1ns;
      dst_clk_i = 0;
      #1ns;
    end
  end

endmodule
