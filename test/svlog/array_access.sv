module A;
	initial begin
		int a;
		int b;
		b = a[9];
		b = a[15:0];
		a[9] = 1;
		a[15:0] = 42;
		a[b] = 1;
		a[b+:8] = 42;
		a[b-:8] = 42;
	end
endmodule
