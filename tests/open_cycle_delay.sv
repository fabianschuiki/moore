// Test for an endless cycle delay
module A1 (input logic clk_i, input logic data_gnt_i, input logic data_rvalid_i);

    assert property (@(posedge clk_i) data_gnt_i |-> ##[1:$] data_rvalid_i )
        else begin $error("There was a grant without a rvalid"); $stop(); end

endmodule