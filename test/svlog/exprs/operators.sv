// RUN: moore %s -e foo
module foo;
	initial begin
		int a, b, c;

		// Unary operators
		a = +b;
		a = -b;
		a = ~b;
		a = !b;
		a = &b;
		a = ~&b;
		a = |b;
		a = ~|b;
		a = ^b;
		a = ~^b;
		a = ^~b;

		// Increment/decrement operators
		a = b++;
		a = ++b;
		a = b--;
		a = --b;

		// Binary operators
		a = b + c;
		a = b - c;
		a = b * c;
		a = b / c;
		// a = b ** c; // not yet supported
		a = b == c;
		a = b != c;
		a = b === c;
		a = b !== c;
		a = b ==? c;
		a = b !=? c;
		a = b < c;
		a = b <= c;
		a = b > c;
		a = b >= c;
		a = b << c;
		a = b <<< c;
		a = b >> c;
		a = b >>> c;
		a = b & c;
		a = b ~& c;
		a = b | c;
		a = b ~| c;
		a = b ^ c;
		a = b ~^ c;
		a = b ^~ c;
		a = b && c;
		a = b || c;
		a = b == c ? 42 : 9001;

		// Cast operators
	    a = unsigned'(b);
	    a = signed'(b);
	    a = $unsigned(b);
	    a = $signed(b);
	end
endmodule
