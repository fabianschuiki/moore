module A;
    typedef int x_t;
    typedef logic y_t;
    typedef x_t z_t;
    x_t x;
    y_t y;
    z_t z;
endmodule

//@ elab A
//| entity @A () () {
//|     %x = sig i32
//|     %y = sig i1
//|     %z = sig i32
//| }
