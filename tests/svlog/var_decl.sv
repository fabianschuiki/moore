module A;
	int x;
	initial for (int i = 0, n = 42; i < 16; i++) #1ns x = i;
endmodule
