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
	B #(a * b) b11();
	B #(a / b) b12();
	B #(a % b) b13();
	B #(a << b) b14();
	B #(a <<< b) b15();
	B #(a >> b) b16();
	B #(a >>> b) b17();
	B #(a == b ? 42 : 9001) b18();
	B #(a != b ? 42 : 9001) b19();
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
//| entity @B.param11 () () {
//|     %x = sig i32 798
//| }
//|
//| entity @B.param12 () () {
//|     %x = sig i32 2
//| }
//|
//| entity @B.param13 () () {
//|     %x = sig i32 4
//| }
//|
//| entity @B.param14 () () {
//|     %x = sig i32 22020096
//| }
//|
//| entity @B.param15 () () {
//|     %x = sig i32 22020096
//| }
//|
//| entity @B.param16 () () {
//|     %x = sig i32 0
//| }
//|
//| entity @B.param17 () () {
//|     %x = sig i32 0
//| }
//|
//| entity @B.param18 () () {
//|     %x = sig i32 9001
//| }
//|
//| entity @B.param19 () () {
//|     %x = sig i32 42
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
//|     %b11 = inst @B.param11 () ()
//|     %b12 = inst @B.param12 () ()
//|     %b13 = inst @B.param13 () ()
//|     %b14 = inst @B.param14 () ()
//|     %b15 = inst @B.param15 () ()
//|     %b16 = inst @B.param16 () ()
//|     %b17 = inst @B.param17 () ()
//|     %b18 = inst @B.param18 () ()
//|     %b19 = inst @B.param19 () ()
//| }
