module A;
	B b();
endmodule

module B;
endmodule

//@ elab A
//| entity @B () () {
//| }
//|
//| entity @A () () {
//|     inst @B () ()
//| }

module C;
	D #(void) d1();
	D #(bit) d2();
endmodule

module D #(type T) (input T t);
endmodule

//@ elab C
//| entity @D.param1 (void$ %t) () {
//| }
//|
//| entity @D.param2 (i1$ %t) () {
//| }
//|
//| entity @C () () {
//|     inst @D.param1 () ()
//|     inst @D.param2 () ()
//| }

// Default types
module E #(type T = bit) (input T t);
endmodule

//@ elab E
//| entity @E (i1$ %t) () {
//| }
