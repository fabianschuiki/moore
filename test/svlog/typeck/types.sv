// RUN: moore %s

module foo;
    // Integer types
    bit      v0;
    logic    v1;
    reg      v2;
    byte     v3;
    shortint v4;
    int      v5;
    longint  v6;
    integer  v7;
    time     v8;

    // Signing
    bit unsigned v9;
    bit signed   v10;

    // Packed dimensions
    bit [41:0]      v11;
    bit [41:0][3:0] v12;

    // Non-integer types
    shortreal v13;
    real      v14;
    realtime  v15;

    // Other types
    string  v16;
    chandle v17;
    event   v18;

    // Variable dimensions
    bit v19 [];
    bit v20 [4];
    bit v21 [4:0];
    bit v22 [string];
    bit v23 [*];
    bit v24 [$];
    bit v25 [$:4];

    // Module instances
    bar m0 ();
    bar m1 [2] ();
    bar m2 [1:0] ();
    bar m3 [2][3] ();

    // Interface instances
    baz i0 ();
    baz i1 [2] ();
    baz i2 [1:0] ();
    baz i3 [2][3] ();
endmodule
