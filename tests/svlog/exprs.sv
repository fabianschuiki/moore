module A;
	int a, b, c;
	initial begin
		#1ns a = ~b;
		#1ns a = b++;
		#1ns a = ++b;
		#1ns a = b--;
		#1ns a = --b;
		// a = 1 + 2;
		// a = b + 1;
		// a = b + c;
		// a = b - c;
		// a = b * c;
		// a = b / c;
		// a = b & c;
		// a = b | c;
		// a = b ^ c;
		#1ns;
	end
endmodule

//@ elab A
