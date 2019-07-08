module alu;
	initial case (blub) inside
        [(dm::Data0):DataEnd]: begin
        end
    endcase

    initial if (data inside {[3'b000:3'b100], 3'b111}) begin
    end
endmodule
