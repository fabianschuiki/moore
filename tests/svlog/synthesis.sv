module synth_input (
	input logic clk_i,
	input logic rst_ni
);
	logic [7:0] a, b;
	assign a = 8'd42 ^ b;
endmodule
