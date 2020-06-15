// RUN: moore %s -e foo -e bar
// IGNORE  see #190

module foo;
	int i;
	initial for (i = 1; i < 16; i = i + 1);
endmodule
