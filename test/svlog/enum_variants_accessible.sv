module barrier #(
  parameter int NrPorts = 4,
  parameter type req_t = logic [31:0]
) (
  input  logic clk_i,
  input  logic rst_i,
  input  req_t [NrPorts-1:0] in_addr_i,
  input  logic [NrPorts-1:0] in_valid_i,
  output logic [NrPorts-1:0] in_ready_o,
  output logic [NrPorts-1:0] out_valid_o,
  input  logic [NrPorts-1:0] out_ready_i
);

  enum logic [1:0] {
    Idle,
    Wait,
    Take
  } [NrPorts-1:0] state_d, state_q;
  logic [NrPorts-1:0] is_barrier;
  logic take_barrier;

  assign take_barrier = &is_barrier;
  localparam logic [31:0] BarrierReg = 32'h1234beef;

  always_comb begin
    state_d     = state_q;
    is_barrier  = '0;
    out_valid_o = in_valid_i;
    in_ready_o  = out_ready_i;

    for (int i = 0; i < NrPorts; i++) begin
      case (state_q[i])
        Idle: begin
          if (in_valid_i[i] && (in_addr_i[i] == BarrierReg)) begin
            state_d[i] = Wait;
            out_valid_o[i] = 0;
            in_ready_o[i]  = 0;
          end
        end
        Wait: begin
          is_barrier[i]  = 1;
          out_valid_o[i] = 0;
          in_ready_o[i]  = 0;
          if (take_barrier) state_d[i] = Take;
        end
        Take: begin
          if (out_valid_o[i] && in_ready_o[i]) state_d[i] = Idle;
        end
        default: state_d[i] = Idle;
      endcase
    end
  end

  for (genvar i = 0; i < NrPorts; i++) begin : gen_ff
    always_ff @(posedge clk_i, posedge rst_i)
      state_q[i] = rst_i ? Idle : state_d[i];
  end

endmodule
