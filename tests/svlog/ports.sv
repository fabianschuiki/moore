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
//| proc @D.initial.238.0 (i1$ %0) (i1$ %1) {
//| %2:
//|     %x = prb %0
//|     %3 = not i1 %x
//|     drv %1 %3 0s 1e
//|     wait %6 for 0s 1e
//| %6:
//|     halt
//| }
//|
//| entity @D (i1$ %x) (i1$ %y) {
//|     inst @D.initial.238.0 (%x) (%y)
//| }
