module top;
	bit clk = 0;
	bit rst_n = 1;
	int count = 99;

	always_ff @(posedge clk, negedge rst_n) begin
		if (!rst_n)
			count = 0;
		else
			count++;
	end

	initial begin
		#1ns rst_n = 0;
		#1ns rst_n = 1;
		#1ns clk = ~clk;
		#1ns clk = ~clk;
		#1ns clk = ~clk;
		#1ns clk = ~clk;
		#1ns clk = ~clk;
		#1ns clk = ~clk;
		#1ns clk = ~clk;
		#1ns clk = ~clk;
		#1ns;
	end
endmodule
