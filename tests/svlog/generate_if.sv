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
