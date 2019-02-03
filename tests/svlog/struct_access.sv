module A;
	initial begin
		struct {
			int a;
		} x;
		int y;
		// x.a = 42;
		// y = x.b;
		y = x.a;
	end
endmodule
