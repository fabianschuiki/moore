package foo;
	localparam int magic = 42;
endpackage

module bar;
	import foo::*;
	int baz;
	initial baz = magic;
endmodule

//@ elab bar
