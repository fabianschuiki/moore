module A;
	var k0 = '0;
	var k1 = '1;
	var k2 = 'h3;
	var k3 = 'b100111;
	var k4 = 'o777;
	var k5 = 'd42;
	var k6 = 32'h3;
	var k7 = 64'b100111;
	var k8 = 16'o777;
	var k9 = 9001'd42;
endmodule

//@ elab A
//| entity @A () () {
//|     %k0 = sig i1 0
//|     %k1 = sig i1 1
//|     %k2 = sig i2 3
//|     %k3 = sig i6 39
//|     %k4 = sig i9 511
//|     %k5 = sig i6 42
//|     %k6 = sig i32 3
//|     %k7 = sig i64 39
//|     %k8 = sig i16 511
//|     %k9 = sig i9001 42
//| }
