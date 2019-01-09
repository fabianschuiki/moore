module A;
	int a;
	int b;
	int c;

	initial;

	initial a = 42;

	initial b = a;

	initial begin
	end

	initial begin
		c = 0;
		c = 1;
		c = a;
	end
endmodule
