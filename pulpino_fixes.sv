// Since we currently don't support VHDL, there is no way of compiling the
// apb_uart entity.
module apb_uart (
	input logic CLK,
	input logic RSTN,
	input logic PSEL,
	input logic PENABLE,
	input logic PWRITE,
	input logic [2:0] PADDR,
	input logic [31:0] PWDATA,
	output logic [31:0] PRDATA,
	output logic PREADY,
	output logic PSLVERR,
	output logic INT,
	output logic OUT1N,
	output logic OUT2N,
	output logic RTSN,
	output logic DTRN,
	input logic CTSN,
	input logic DSRN,
	input logic DCDN,
	input logic RIN,
	input logic SIN,
	output logic SOUT
);

	assign PREADY = 0;
	assign PSLVERR = 0;
	assign INT = 0;
	assign OUT1N = 0;
	assign OUT2N = 0;
	assign RTSN = 0;
	assign DTRN = 0;
	assign SOUT = 0;

endmodule
