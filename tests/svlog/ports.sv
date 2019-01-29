module A;
endmodule

//@ elab A
//| entity @A () () {
//| }


module B (
    input bit x,
    output bit y,
    inout bit z
);
endmodule

//@ elab B
//| entity @B (i1$ %x, i1$ %z) (i1$ %y, i1$ %z0) {
//|     drv %y 0
//|     drv %z0 0
//| }


module C (
    output bit x = 0,
    output bit y = 1
);
endmodule

//@ elab C
//| entity @C () (i1$ %x, i1$ %y) {
//|     drv %x 0
//|     drv %y 1
//| }


module D (
	input bit x,
	output bit y
);
	initial y = ~x;
endmodule

//@ elab D
//| proc @n226 (i1$ %0) (i1$ %1) {
//| %2:
//|     %3 = prb %0
//|     %4 = not i1 %3
//|     drv %1 %4
//|     halt
//| }
//|
//| entity @D (i1$ %x) (i1$ %y) {
//|     inst @n226 (%x) (%y)
//| }
