// @exclude
module typedef_enum (
    input logic clk_i,
    input logic rst_ni
);
    typedef enum logic [1:0] { IDLE, BUSY, FAILED } state_t;
    state_t state_d, state_q;

    always_comb begin
        state_d = state_q;
        case (state_q)
            IDLE: begin
                state_d = BUSY;
            end
            BUSY: begin
                state_d = FAILED;
            end
        endcase
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (rst_ni == 1'b0) begin
            state_q <= IDLE;
        end else begin
            state_q <= state_d;
        end
    end
endmodule
