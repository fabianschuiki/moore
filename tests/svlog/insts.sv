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

module D #(type T);
endmodule
