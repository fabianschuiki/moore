module A (input int a, input int b, output int c);
	assign c = a + b;
endmodule

//@ elab A
//| entity @A (i32$ %a, i32$ %b) (i32$ %c) {
//|     %0 = prb %a
//|     %1 = prb %b
//|     %2 = add i32 %0 %1
//|     %3 = sig i32
//|     drv %3 %2
//|     drv %c %3
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
