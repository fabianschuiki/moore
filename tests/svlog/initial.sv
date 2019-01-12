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
		#5ns;
		c = 1;
		#5ns;
		c = a;
		#5ns;
	end
endmodule
