module A;
	initial begin
		struct {
			int a;
			shortint b;
		} x;
		int y;
		// x.a = 42;
		y = x.a;
		y = x.b;
	end
endmodule
