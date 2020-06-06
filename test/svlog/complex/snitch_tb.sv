// RUN: moore %s -e snitch_tb snitch.sv -O0

module snitch_tb;
	localparam logic [31:0] BootAddr = 32'h0001_0000;

	logic clk_i;
	logic rst_i = 1'b0;

	logic [31:0]   inst_addr_o;
	logic [31:0]   inst_data_i;
	logic          inst_valid_o;
	logic          inst_ready_i;

	logic [31:0]   data_qaddr_o;
	logic          data_qwrite_o;
	logic [3:0]    data_qamo_o;
	logic [63:0]   data_qdata_o;
	logic [7:0]    data_qstrb_o;
	logic          data_qvalid_o;
	logic          data_qready_i;
	logic [63:0]   data_pdata_i;
	logic          data_perror_i;
	logic          data_pvalid_i;
	logic          data_pready_o;

	snitch #(
  		.BootAddr(BootAddr),
		.RVFD(0)
	) i_snitch (
		.clk_i,
		.rst_i,
		.hart_id_i(32'h42),

		.inst_addr_o,
		.inst_data_i,
		.inst_valid_o,
		.inst_ready_i,

		.data_qaddr_o,
		.data_qwrite_o,
		.data_qamo_o,
		.data_qdata_o,
		.data_qstrb_o,
		.data_qvalid_o,
		.data_qready_i,
		.data_pdata_i,
		.data_perror_i,
		.data_pvalid_i,
		.data_pready_o
	);

	logic [15:0][31:0] PROGRAM;
	assign PROGRAM = '{
		0:  /* 10000 */ 32'h 3e800713, // li      a4,1000
		1:  /* 10004 */ 32'h 00100793, // li      a5,1
		2:  /* 10008 */ 32'h 00000613, // li      a2,0
		3:  /* 1000c */ 32'h cafe15b7, // lui     a1,0xcafe1
		4:  /* 10010 */ 32'h 00f606b3, // add     a3,a2,a5
		5:  /* 10014 */ 32'h 00d5a023, // sw      a3,0(a1) # cafe1000 <__global_pointer$+0xcafcf7cc>
		6:  /* 10018 */ 32'h fff70713, // addi    a4,a4,-1
		7:  /* 1001c */ 32'h 00078613, // mv      a2,a5
		8:  /* 10020 */ 32'h 00068793, // mv      a5,a3
		9:  /* 10024 */ 32'h fe0716e3, // bnez    a4,10010 <_start+0x10>
		10: /* 10028 */ 32'h 10500073, // wfi
		11: /* 1002c */ 32'h ffdff06f, // j       10028 <_start+0x28>
		12: /* 10030 */ 32'h 00008067, // ret
		default: '0
	};

	assign inst_data_i = PROGRAM[(inst_addr_o - BootAddr) / 4];
	assign inst_ready_i = 1;

	int data_resp_pending = 0;
	always @(posedge clk_i) begin
		if (data_pvalid_i && data_pready_o)
			data_resp_pending--;
		if (data_qvalid_o && data_qready_i)
			data_resp_pending++;
	end
	assign data_qready_i = 1;
	assign data_pdata_i = 32'h deadcab0;
	assign data_perror_i = 0;
	assign data_pvalid_i = (data_resp_pending > 0);

	initial begin
		rst_i <= #1ns 1;
		clk_i <= #2ns 1;
		clk_i <= #3ns 0;
		rst_i <= #4ns 0;
		#5ns;
		repeat (1000000) begin
			clk_i = 1;
			#1ns;
			clk_i = 0;
			#1ns;
		end
		#1ns;
	end

endmodule
