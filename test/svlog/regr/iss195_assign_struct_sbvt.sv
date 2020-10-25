// RUN: moore %s -e foo
// IGNORE  see #195

module foo;
	struct packed {
        logic [1:0] a;
        logic [2:0] b;
        logic [3:0] c;
    } [3:0] x;
    initial begin
    	x[0][0] = 1; // bit 0 of c
    	x[0][4] = 1; // bit 0 of b
    	x[0][7] = 1; // bit 0 of a
    end
endmodule
