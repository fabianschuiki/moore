module A #(int a = 42, bit [63:0][15:0] b = '0);
	B #($clog2(a)) b1();
	B #($bits(b)) b2();

	initial begin
		int k;
		k = $clog2(a);
		k = $bits(b);
	end
endmodule

module B #(int K);
	int x = K;
endmodule

//@ elab A
//| entity @B.param1 () () {
//|     %x = sig i32 6
//| }
//|
//| entity @B.param2 () () {
//|     %x = sig i32 1024
//| }
//|
//| proc @A.initial.228.0 () () {
//| %0:
//|     %k = var i32
//|     store i32 %k 6
//|     store i32 %k 1024
//|     halt
//| }
//|
//| entity @A () () {
//|     %b1 = inst @B.param1 () ()
//|     %b2 = inst @B.param2 () ()
//|     inst @A.initial.228.0 () ()
//| }
