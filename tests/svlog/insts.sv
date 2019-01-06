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
	D #(0) d1();
	D #(1) d2();
endmodule

module D #(x);
endmodule
