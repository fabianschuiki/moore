// RUN: moore %s -e A -e C

module A (input int a, input int b, output int c);
	assign c = a + b;
endmodule

// CHECK: entity @A (i32$ %a, i32$ %b) -> (i32$ %c) {
// CHECK:     %a1 = prb i32$ %a
// CHECK:     %b1 = prb i32$ %b
// CHECK:     %0 = add i32 %a1, %b1
// CHECK:     %1 = const time 0s 1e
// CHECK:     drv i32$ %c, %0, %1
// CHECK: }

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

//| proc @C.initial.237.0 () (i32$ %0) {
//| %1:
//|     drv %0 9001 0s 1d
//|     drv %0 42 1ns
//|     halt
//| }
//|
//| entity @C () () {
//|     %a = sig i32
//|     inst @C.initial.237.0 () (%a)
//| }

module D;
	initial begin
		int a, b;
		a += b;
		a -= b;
		a *= b;
		a /= b;
		a %= b;
		a &= b;
		a |= b;
		a ^= b;
		a <<= b;
		a <<<= b;
		a >>= b;
		a >>>= b;
	end
endmodule
