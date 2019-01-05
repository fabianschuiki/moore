// Array query functions
// 20.7 of std-2009

// @elab A
module A;

	// Dimension numbers
	//      3    4       1    2
	// logic [3:0][2:1] n1 [1:5][2:8];
	// typedef logic [3:0][2:1] packed_reg;
	// packed_reg n2[1:5][2:8]; // same dimensions as in the lines above

	// localparam dn1 = $dimensions(n1), udn1 = $unpacked_dimensions(n1);
	// localparam dn2 = $dimensions(n2), udn2 = $unpacked_dimensions(n2);
	// localparam len1 = $left(n1);
	// localparam rin1 = $right(n1);
	// localparam lon1 = $low(n1);
	// localparam hin1 = $high(n1);
	// localparam inn1 = $increment(n1);
	// localparam sin1 = $size(n1);

	// TODO: Check that
	// - dn1 = 4
	// - dn2 = 4
	// - udn1 = 2
	// - udn2 = 2


	// Fixed-size integers
	integer [3:0] m1;
	shortint [3:0] m2;
	longint [3:0] m3;
	byte [3:0] m4;

	localparam dm1 = $dimensions(m1), udm1 = $unpacked_dimensions(m1);
	localparam dm2 = $dimensions(m2), udm2 = $unpacked_dimensions(m2);
	localparam dm3 = $dimensions(m3), udm3 = $unpacked_dimensions(m3);
	localparam dm4 = $dimensions(m4), udm4 = $unpacked_dimensions(m4);
	localparam lem1d1 = $left(m1,1), lem1d2 = $left(m1,2);
	localparam rim1d1 = $right(m1,1), rim1d2 = $right(m1,2);
	localparam lom1d1 = $low(m1,1), lom1d2 = $low(m1,2);
	localparam him1d1 = $high(m1,1), him1d2 = $high(m1,2);
	localparam inm1d1 = $increment(m1,1), inm1d2 = $increment(m1,2);
	localparam sim1d1 = $size(m1,1), sim1d2 = $size(m1,2);

	// TODO: Check that
	// - dm1 = 2
	// - dm2 = 2
	// - dm3 = 2
	// - dm4 = 2




	// Integers without range specifier
	localparam p1 = 2;
	localparam p2 = 3;
	localparam p3 = 4;

	// localparam dp1 = $dimensions(p1);
	// localparam dp2 = $dimensions(p2);
	// localparam dp3 = $dimensions(p3);

	// TODO: Check that
	// - dp1 = 1
	// - dp2 = 1
	// - dp3 = 1


	// Types equivalent to a simple bit vector
	string q1;
	enum { KA, KB } q2;
	// struct { logic a; } q3;

	// localparam dq1 = $dimensions(q1);
	// localparam dq2 = $dimensions(q2);
	// localparam dq3 = $dimensions(q3);

	// TODO: Check that
	// - dq1 = 1
	// - dq2 = 1
	// - dq3 = 1


	// Type as first argument
	// localparam d1 = $dimensions(integer),  ud1 = $dimensions(integer);
	// localparam d2 = $dimensions(shortint), ud2 = $dimensions(shortint);
	// localparam d3 = $dimensions(longint),  ud3 = $dimensions(longint);

endmodule
