module top;
	bit clk = 0;
	int count = 0;
	always @(posedge clk) count = ++count;
	always #1ns clk = ~clk;
endmodule
