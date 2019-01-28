module alu (
	input int a,
	input int b,
	input bit op,
	output int z
);
	always_comb begin
		if (op == 0) begin
			z = a + b;
		end else begin
			z = a - b;
		end
	end
endmodule

module top;
	int a, b, c;
	bit op;

	alu i_alu(a, b, op, z);

	initial repeat (8) begin
		a++;
		b++;
		b++;
		op = ~op;
		#1ns;
	end
endmodule
