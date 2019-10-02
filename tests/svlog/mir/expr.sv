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
