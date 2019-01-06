module foo;
	bar b();
endmodule

module bar;
endmodule

//@ elab foo
//| entity @bar () () {
//| }
//|
//| entity @foo () () {
//|     inst @bar () ()
//| }
