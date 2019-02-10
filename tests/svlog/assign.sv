module A (input int a, input int b, output int c);
	assign c = a + b;
endmodule

//@ elab A
//| entity @A (i32$ %a, i32$ %b) (i32$ %c) {
//|     %a0 = prb %a
//|     %b0 = prb %b
//|     %0 = add i32 %a0 %b0
//|     %1 = sig i32
//|     drv %1 %0
//|     drv %c %1
//| }

module B;
	int a, b, c;
	A adder(a, b, c);
	initial #1ns repeat(8) begin
		a = a + 1;
		b = b + 2;
		#1ns;
	end
endmodule

module C;
	int a;
	initial begin
		a <= 9001;
		a <= #1ns 42;
	end
endmodule

//@ elab C
//| proc @C.initial.236.0 () (i32$ %0) {
//| %1:
//|     drv %0 9001 0s 1d
//|     drv %0 42 1ns
//|     halt
//| }
//|
//| entity @C () () {
//|     %a = sig i32
//|     inst @C.initial.236.0 () (%a)
//| }
