module fir #(
	parameter int T = 4,
	parameter int NI = 8,
	parameter int NO = 2*NI
) (
	input logic CLK,
	input logic [NI-1:0] X,
	input logic [T-1:0][NI-1:0] W,
	output logic [NO-1:0] Y
);

	logic [T-1:0][NO-1:0] mul_out, add_out, q;

	for (genvar i = 0; i < T; i++)
		assign mul_out[i] = W[i] * X;

	for (genvar i = 0; i < T; i++)
		assign add_out[i] = q[i] + mul_out[T-i-1];

	assign q[0] = '0;
	for (genvar i = 1; i < T; i++)
		always_ff @(posedge CLK) q[i] <= add_out[i-1];

	assign Y = add_out[T-1];

endmodule
