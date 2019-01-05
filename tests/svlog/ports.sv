module A;
endmodule

module B (
	input bit x,
	output bit y,
	inout bit z
);
endmodule

//@ elab A
//| entity @A () () {
//| }

//@ elab B
//| entity @B (i1$ %x, i1$ %z) (i1$ %y, i1$ %z0) {
//| }
