// RUN: moore %s -e foo -O0
// Currently broken without `-O0`; see issue #164.

module foo;
	int a;
	bit b;
	initial forever b = 1;
	initial repeat (10) b = 1;
	initial while (10 > 9) b = 1;
	initial do b = 1; while (7 > 5);
	initial for (a = 0; a < 4; a++) b = 1;
endmodule
