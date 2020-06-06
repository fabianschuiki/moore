// RUN: moore %s -e stream_delay_tb stream_delay.sv counter.sv delta_counter.sv lfsr_16bit.sv -O0

// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba, zarubaf@iis.ee.ethz.ch
// Description: Delay (or randomize) AXI-like handshaking

module stream_delay_tb;

    logic clk_i;
    logic rst_ni = 1'b1;

    int   payload_i;
    logic ready_o;
    logic valid_i;

    int   payload_o;
    logic ready_i;
    logic valid_o;

    stream_delay #(
        .StallRandom(1),
        .FixedDelay(0),
        .payload_t(int)
    ) dut (
        .clk_i(clk_i),
        .rst_ni(rst_ni),

        .payload_i(payload_i),
        .ready_o(ready_o),
        .valid_i(valid_i),

        .payload_o(payload_o),
        .ready_i(ready_i),
        .valid_o(valid_o)
    );


    initial begin
        rst_ni <= #1ns 0;
        rst_ni <= #2ns 1;
        #4ns;
        repeat (600000) begin
            clk_i <= #1ns 1;
            clk_i <= #2ns 0;
            #2ns;
        end
    end

    assign valid_i = 1;
    always @(posedge clk_i iff ready_o) payload_i <= #0.5ns payload_i + 1;

    assign ready_i = valid_o;

endmodule
