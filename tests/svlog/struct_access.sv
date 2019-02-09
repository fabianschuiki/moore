module A;
	initial begin
		struct {
			int a;
			shortint b;
		} x;
		int y;
		y = x.a;
		y = x.b;
		x.a = 42;
		x.b = 42;
	end
endmodule
