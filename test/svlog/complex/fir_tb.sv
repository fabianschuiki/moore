// RUN: moore %s -e fir_tb fir.sv -O0

timeunit 1ns/1ps;

module fir_tb;

    localparam int T = 4;
    localparam int NI = 8;
    localparam int NO = 2*NI;

    logic CLK;
    logic [NI-1:0] X;
    logic [T-1:0][NI-1:0] W;
    logic [NO-1:0] Y;

    fir #(
        .T(T),
        .NI(NI),
        .NO(NO)
    ) dut (
        .CLK(CLK),
        .X(X),
        .W(W),
        .Y(Y)
    );

    assign W[0] = -2;
    assign W[1] = -1;
    assign W[2] = 3;
    assign W[3] = 4;

    initial begin
        X <= '0;
        repeat (5000000) begin
            CLK <= #1ns 1;
            CLK <= #2ns 0;
            #2ns;
        end
    end

    always @(posedge CLK) X <= #0.5ns (X + 9) % 19;

endmodule
