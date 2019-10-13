// 11.6 Expression bit lengths
// Expressions inherit bit length from arguments and assignment context.
module a0;
	logic [14:0] a;
	logic [15:0] b;
	logic [15:0] sumA;
	logic [16:0] sumB;

	assign sumA = a + b; // addition on 16 bits
	// v0 = Var(a) @ logic [14:0]
	// v1 = Zext(v0, 16) @ logic [15:0]
	// v2 = Var(b) @ logic [15:0]
	// v3 = IntBinaryArith(Add, unsigned, 16, v1, v2) @ logic [15:0]

	assign sumB = a + b; // addition on 17 bits
	// v0 = Var(a) @ logic [14:0]
	// v1 = Zext(v0, 17) @ logic [16:0]
	// v2 = Var(b) @ logic [15:0]
	// v3 = Zext(v2, 17) @ logic [16:0]
	// v4 = IntBinaryArith(Add, unsigned, 17, v1, v3) @ logic [16:0]

	assign sumB = {a + b}; // addition on 16 bits, then cast to 17 bits
	// v0 = Var(a) @ logic [14:0]
	// v1 = Zext(v0, 16) @ logic [15:0]
	// v2 = Var(b) @ logic [15:0]
	// v3 = IntBinaryArith(Add, unsigned, 16, v1, v2) @ logic [15:0]
	// v4 = Zext(v3, 17) @ logic [16:0]
endmodule

// 11.4.12 Concatenation operators
module a1;
	logic a;
	logic [7:0] b;
	logic w;
	logic [8:0] z;
	assign z = {a, b[3:0], w, 3'b101};
endmodule

// Sign casts
module a2;
	logic unsigned [7:0] a;
	logic signed [7:0] b;
	logic [7:0] z;
	assign z = $signed(a);
	assign z = $unsigned(b);
endmodule

// 11.5.1 Vector bit-select and part-select addressing
module a3;
	logic [31: 0] a_vect;
	logic [0 :31] b_vect;
	logic [63: 0] dword;
	integer sel;
	logic [7:0] z;
	logic y;

	assign z = a_vect[ 7 : 0];
	assign z = a_vect[15 : 8];
	assign z = b_vect[0 : 7];
	assign z = b_vect[8 :15];

	assign z = a_vect[ 0 +: 8];
    assign z = a_vect[15 -: 8];
    assign z = b_vect[ 0 +: 8];
    assign z = b_vect[15 -: 8];
    assign z = dword[8*sel +: 8];

    assign y = a_vect[15];
    assign y = b_vect[15];
    assign y = dword[15];
    assign y = a_vect[sel];
    assign y = b_vect[sel];
    assign y = dword[sel];
endmodule

// Member accesses
module a4;
	struct packed {
		logic [1:0] a;
		logic [4:0] b;
	} s;
	logic [1:0] y;
	logic [4:0] z;
	assign y = s.a;
	assign z = s.b;
endmodule
