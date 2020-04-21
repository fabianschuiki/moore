module A;
    for (genvar i = 0; i < 4; i++)
        B b();
endmodule

module B;
endmodule

//@ elab A
//| entity @B () () {
//| }
//|
//| entity @A () () {
//|     %b = inst @B () ()
//|     %b0 = inst @B () ()
//|     %b1 = inst @B () ()
//|     %b2 = inst @B () ()
//| }
