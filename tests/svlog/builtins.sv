module A #(int a = 42);
	B #($clog2(a)) b1();
endmodule

module B #(int K);
	int x = K;
endmodule

//@ elab A
//| entity @B.param1 () () {
//|     %x = sig i32 6
//| }
//|
//| entity @A () () {
//|     %b1 = inst @B.param1 () ()
//| }
