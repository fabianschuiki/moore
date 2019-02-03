module A;
  B #(11) b1();
  B #(13) b2();
endmodule

module B #(int K);
    int x = K;
    if (K > 12)
        initial x = 42;
    else
        initial x = 19;
endmodule

//@ elab A
//| proc @n235 () (i32$ %0) {
//| %1:
//|     drv %0 19 1e
//|     wait %4 for 1e
//| %4:
//|     halt
//| }
//|
//| entity @B.param1 () () {
//|     %x = sig i32 11
//|     inst @n235 () (%x)
//| }
//|
//| proc @n234 () (i32$ %0) {
//| %1:
//|     drv %0 42 1e
//|     wait %4 for 1e
//| %4:
//|     halt
//| }
//|
//| entity @B.param2 () () {
//|     %x = sig i32 13
//|     inst @n234 () (%x)
//| }
//|
//| entity @A () () {
//|     %b1 = inst @B.param1 () ()
//|     %b2 = inst @B.param2 () ()
//| }
