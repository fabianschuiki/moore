// RUN: moore %s -e graycode_tb graycode.sv -O0

// Copyright 2018 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

timeunit 1ns/1ns;

module graycode_tb #(
    parameter int N = 20
);

    logic [N-1:0] a, b, c, bp;

    graycode #(N) dut (a,b,c);

    task check;
        assert(a == c);
        assert($signed($countones(b) - $countones(bp)) inside {-1,0,1});
        bp = b;
    endtask

    initial begin : p_stim
        logic [N:0] i;
        bp = '0;

        // Count up twice, including overflow.
        repeat(2) for (i = 0; i < 1 << N; i++) begin
            a = i;
            #1ns;
            assert(a == c);
            assert($signed($countones(b) - $countones(bp)) inside {-1,0,1});
            bp = b;
        end

        // Count backwards.
        for (i = 0; i < 1 << N; i++) begin
            a = ((1 << N)-i)-1;
            #1ns;
            assert(a == c);
            assert($signed($countones(b) - $countones(bp)) inside {-1,0,1});
            bp = b;
        end
    end

endmodule
