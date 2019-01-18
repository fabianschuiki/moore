module A #(K);
    for (genvar i = 0; i < K; i++)
        B b();
endmodule

module B;
endmodule
