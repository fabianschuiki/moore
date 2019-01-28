module A;
    parameter int K = 12;
    localparam int N = K+1;
    int a = N;
endmodule

module B;
	A #(42) a();
endmodule
