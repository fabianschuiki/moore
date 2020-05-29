// 6.20 of svlog-2009

module A1 #(int a = 5, localparam logic b = 1, type c = int, parameter n);
	// TODO: Check that parameter port is
	// - parameter int a = 5,
	// - localparam logic b = 1,
	// - localparam type c = int,
	// - parameter n
endmodule

module A2;
	A1 #(.n(2)) a;
	// TODO: Check that
	// - a.a = non-local (int) 5
	// - a.b = local (logic) 1
	// - a.c = local type int
	// - a.n = non-local (int) 2
endmodule

class B #(size = 1);
	logic [size-1:0] v;
endclass

interface C #(AWIDTH = 64, type T = int) (input logic clk);
endinterface

module D #(int N = 5, M = N*16, type T = int, T x = 0)();
endmodule

// class E #(type T, int size);
// 	T words[size];
// endclass

// typedef E#(byte, 1024) F;
