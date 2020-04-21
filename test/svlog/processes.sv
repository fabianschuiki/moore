module a0;
    int x, y;

    initial x = y;
    always x = y;
    always_comb x = y;
    always_latch x <= y;
    always_ff x <= y;
    always @* x = y;
    always @(*) x = y;
    final x = y;
endmodule
