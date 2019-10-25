module a0;
	logic [3:0] a;
	logic [8:0] b;

	assign a = (b + '1);
endmodule

module a1;
	logic [14:0] a;
	logic [15:0] b;
	logic [15:0] sumA;
	logic [16:0] sumB;

	assign sumA = a + b;
	assign sumB = a + b;
	assign sumB = {a + b};
endmodule
