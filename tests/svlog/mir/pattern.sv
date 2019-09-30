module A;
	logic [5:0] a;
	struct { logic x; logic y; } b;

	assign a = '{3: 42, 4: 29, default: 0};
	assign b = '{default: 0};
endmodule
