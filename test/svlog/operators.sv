module A;
	int a, b, c;
	initial begin
		c = a && b;
		c = a || b;
		c = a & b;
		c = a ~& b;
		c = a | b;
		c = a ~| b;
		c = a ^ b;
		c = a ~^ b;
		c = a ^~ b;
		c = a + b;
		c = a - b;
		c = a * b;
		c = a / b;
		c = a % b;
		c = a << b;
		c = a <<< b;
		c = a >> b;
		c = a >>> b;
	end
endmodule

//@ elab A
