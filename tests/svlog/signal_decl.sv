///////////////////////////////
///  Signal initial values  ///
///////////////////////////////

module A #(int K = 9001);
    int a;
    int b = 42;
    int c = K;
endmodule

module B;
    A #(1) a1();
endmodule

//@ elab A
//| entity @A () () {
//|     %a = sig i32
//|     %b = sig i32 42
//|     %c = sig i32 9001
//| }

//@ elab B
//| entity @A.param1 () () {
//|     %a = sig i32
//|     %b = sig i32 42
//|     %c = sig i32 1
//| }
//|
//| entity @B () () {
//|     %a1 = inst @A.param1 () ()
//| }
