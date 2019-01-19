module A #(int a = 42, int b = 19);
	B #(a + b) b1();
	B #(a - b) b2();
	B #(a == b) b3();
	B #(a != b) b4();
	B #(a >= b) b5();
	B #(a > b) b6();
	B #(a <= b) b7();
	B #(a < b) b8();
	B #(!a) b9();
	B #(~a) b10();
endmodule

module B #(int K);
	int x = K;
endmodule

//@ elab A
//| entity @B.param1 () () {
//|     %x = sig i32 61
//| }
//|
//| entity @B.param2 () () {
//|     %x = sig i32 23
//| }
//|
//| entity @B.param3 () () {
//|     %x = sig i32 0
//| }
//|
//| entity @B.param4 () () {
//|     %x = sig i32 1
//| }
//|
//| entity @B.param5 () () {
//|     %x = sig i32 1
//| }
//|
//| entity @B.param6 () () {
//|     %x = sig i32 1
//| }
//|
//| entity @B.param7 () () {
//|     %x = sig i32 0
//| }
//|
//| entity @B.param8 () () {
//|     %x = sig i32 0
//| }
//|
//| entity @B.param9 () () {
//|     %x = sig i32 0
//| }
//|
//| entity @B.param10 () () {
//|     %x = sig i32 4294967253
//| }
//|
//| entity @A () () {
//|     %b1 = inst @B.param1 () ()
//|     %b2 = inst @B.param2 () ()
//|     %b3 = inst @B.param3 () ()
//|     %b4 = inst @B.param4 () ()
//|     %b5 = inst @B.param5 () ()
//|     %b6 = inst @B.param6 () ()
//|     %b7 = inst @B.param7 () ()
//|     %b8 = inst @B.param8 () ()
//|     %b9 = inst @B.param9 () ()
//|     %b10 = inst @B.param10 () ()
//| }
