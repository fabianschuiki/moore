module A (input int a, input int b, output int c);
	assign c = a + b;
endmodule

//@ elab A
//| entity @A (i32$ %a, i32$ %b) (i32$ %c) {
//|     %0 = prb %a
//|     %1 = prb %b
//|     %2 = add i32 %0 %1
//|     drv %c %2
//| }
