// RUN: moore %s -e foo
// IGNORE  see #192

module foo;
	genvar i;
    for (i = 0; i < 4; i = i + 1) begin
    end
endmodule
