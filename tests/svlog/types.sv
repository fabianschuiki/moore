module A;
	bit a0;
	int a1;
	bit [41:0] a2;

	logic b0;
	integer b1;
	logic [41:0] b2;

	// enum {
	// 	Foo, Bar
	// } c0;
	// enum int {
	// 	Baz, Buz
	// } c1;
	struct {
		logic a;
		int b;
		struct {
			bit x;
			integer y;
		} c;
	} c2;
endmodule
