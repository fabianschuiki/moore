module port_decl_after_module_dff(clk, reset, d, q);
    input clk;
    input reset;
    input d;
    output reg q;

    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            q <= 1'b0;
        else
            q <= d;
    end
endmodule