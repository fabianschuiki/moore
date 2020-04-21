module a0;
	localparam logic [11:0] CSR_SSR = 12'h7C0;
	logic [31:0] inst_data_i;

	always_comb begin
		if (inst_data_i[31:20] != CSR_SSR) begin
		end
	end
endmodule
