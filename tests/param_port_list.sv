// 6.20 of svlog-2009

class vector #(size = 1);
	logic [size-1:0] v;
endclass

interface simple_bus #(AWIDTH = 64, type T = word) (input logic clk);
endinterface

module mc #(int N = 5, M = N*16, type T = int, T x = 0)();
endmodule

class Mem #(type T, int size);
	T words[size];
endclass

typedef Mem#(byte, 1024) Kbyte;
