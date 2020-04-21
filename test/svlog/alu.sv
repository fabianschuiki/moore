module alu (
	input int a,
	input int b,
	input bit op,
	output int z
);
	always @(a, b, op) begin
		if (op == 0) begin
			z = a + b;
		end else begin
			z = a - b;
		end
	end
endmodule

module top;
	int a, b, z;
	bit op;

	alu i_alu(a, b, op, z);

	initial #1ns repeat (8) begin
		a = a+2;
		b++;
		op = ~op;
		#1ns;
		op = ~op;
		#1ns;
	end
endmodule
