// RUN: moore %s -e A -e B
module A;
    parameter int K = 12;
    localparam int N = K+1;
    int a = N;
endmodule

//@ elab A
//| entity @A () () {
//|     %a = sig i32 13
//| }

module B;
	A #(42) a();
endmodule

//@ elab B
//| entity @A.param1 () () {
//|     %a = sig i32 43
//| }
//|
//| entity @B () () {
//|     %a = inst @A.param1 () ()
//| }
