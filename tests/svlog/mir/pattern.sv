module a0;
	logic [5:0] a;
	struct { logic x; logic y; } b;
	byte c;

	assign a = '{3: 42, 4: 29, default: 0};
	// assign b = '{default: 0};
	// assign c = '{3: 42, 4: 29, default: 0};
endmodule

// 10.9.2 Structure assignment patterns
module a1;
	initial begin
		struct {
			int A;
			struct {
				int B, C;
			} BC1, BC2;
		} ABC, DEF;
		ABC = '{A:1, BC1:'{B:2, C:3}, BC2:'{B:4,C:5}};
		DEF = '{default:10};
	end
endmodule

// Arrays of structures
module a2;
	initial begin
		struct {int a; time b;} abkey[1:0];
		abkey = '{'{a:1, b:2ns}, '{int:5, time:$time}};
	end
endmodule
