module A;
	int a, b, c = 19;
	initial begin
		// #1ns a = +b;
		#1ns a = -b;
		// #1ns a = &b;
		// #1ns a = ~&b;
		// #1ns a = |b;
		// #1ns a = ~|b;
		// #1ns a = ^b;
		// #1ns a = ~^b;
		// #1ns a = ^~b;
		#1ns a = ~b;
		#1ns a = b++;
		#1ns a = ++b;
		#1ns a = b--;
		#1ns a = --b;
		#1ns b = 42;
		#1ns a = 1 + 2;
		#1ns a = b + 1;
		#1ns a = b + c;
		#1ns a = b - c;
		#1ns a = b == c;
		#1ns a = b != c;
		#1ns a = b < c;
		#1ns a = b <= c;
		#1ns a = b > c;
		#1ns a = b >= c;
		#1ns a = !b;
		#1ns a = b && c;
		#1ns a = b || c;
		#1ns a = b == c ? 42 : 9001;
		// a = b * c;
		// a = b / c;
		// a = b & c;
		// a = b | c;
		// a = b ^ c;
		#1ns;
	end
endmodule

//@ elab A
