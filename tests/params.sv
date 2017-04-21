// Parameter dependence
// 23.10.3 of std-2009

module A1;
	parameter
		word_size = 32,
		memory_size = word_size * 4096;
endmodule

// @elab A2
module A2;
	A1 #(.word_size(1)) a1();
	A1 #(.memory_size(16)) a2();
	// TODO: Check that
	// - a1.word_size = 1
	// - a1.memory_size = 4096
	// - a2.word_size = 32
	// - a2.memory_size = 16
endmodule


// The type of parameters can depend on other parameters.
module B1;
	parameter p = 1;
	parameter [p:0] p2 = 4;
	parameter type T = int;
	parameter T p3 = 7;
endmodule

// @elab B2
module B2;
	B1 b1();
	B1 #(.p(2), .T(logic)) b2();
	// TODO: Check that
	// - b1.p = 1
	// - b1.p2 = (logic [1:0]) 0
	// - b1.p3 = (int) 7
	// - b2.p = 2
	// - b2.p2 = (logic [2:0]) 4
	// - b2.p3 = (logic) 1
endmodule


// `T p = 4` is not evaluated if C2 is overridden in the instantiation. It will
// be evaluated and fail if not overridden. `T2 p2 = 4` will only be evaluated
// with the type override provided in the instantiation.
class C1;
endclass

// @elab C2
module C2 #(
	type T = C1, T p = 4,
	type T2, T2 p2 = 4
);
endmodule
