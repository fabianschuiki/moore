// RUN: moore %s -e A

module A;
	int a, b, c;
	initial begin
		a <= +b;
		a <= -b;
		a <= &b;
		a <= ~&b;
		a <= |b;
		a <= ~|b;
		a <= ^b;
		a <= ~^b;
		a <= ^~b;
		a <= ~b;
		a <= b++;
		a <= ++b;
		a <= b--;
		a <= --b;
		a <= 42;
		a <= 1 + 2;
		a <= b + 1;
		a <= b + c;
		a <= b - c;
		a <= b * c;
		a <= b / c;
		// a <= b ** c; // not yet supported
		a <= b & c;
		a <= b | c;
		a <= b ^ c;
		a <= b == c;
		a <= b != c;
		a <= b < c;
		a <= b <= c;
		a <= b > c;
		a <= b >= c;
		a <= !b;
		a <= b && c;
		a <= b || c;
		a <= b == c ? 42 : 9001;
	end
endmodule
