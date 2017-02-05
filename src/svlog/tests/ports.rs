// Copyright (c) 2017 Fabian Schuiki
#![allow(unused_variables)]

mod common;
use common::*;


#[test]
fn empty() {
	compile_to_hir(parse("module foo; endmodule"));
}

#[test]
fn implicit_port() {
	let hir = compile_to_hir(parse("
		module foo (a,b,c);
		endmodule
	"));
	let m = unwrap_single_module(&hir);
}

#[test]
fn impl_ex1() {
	let hir = compile_to_hir(parse("
		module test (a,b,c,d,e,f,g,h);
			input [7:0] a;
			input [7:0] b;
			input signed [7:0] c;
			input signed [7:0] d;
			output [7:0] e;
			output [7:0] f;
			output signed [7:0] g;
			output signed [7:0] h;

			wire signed [7:0] b;
			wire [7:0] c;
			logic signed [7:0] f;
			logic [7:0] g;
		endmodule
	"));
	let m = unwrap_single_module(&hir);

	// TODO: Verify that net `a` is unsigned.
	// TODO: Verify that net port `b` inherits signed attribute from net decl.
	// TODO: Verify that net `c` inherits signed attribute from port.
	// TODO: Verify that net `d` is signed.
	// TODO: Verify that net `e` is unsigned.
	// TODO: Verify that port f inherits signed attribute from logic decl.
	// TODO: Verify that logic g inherits signed attribute from port.
	// TODO: Verify that net `h` is signed.
}

#[test]
fn expl_ex1() {
	let hir = compile_to_hir(parse("
		module test (
			input [7:0] a,
			input signed [7:0] b, c, d,
			output [7:0] e,
			output var signed [7:0] f, g,
			output signed [7:0] h
		);
		endmodule
	"));
	let m = unwrap_single_module(&hir);

	// TODO: Verify that the ports are of the correct size, direction, and type.
	// TODO: Verify that inside the module the appropriate variables and nets
	//       have been declared by the ports.
}

#[test]
#[should_panic]
fn mixed_ansi_and_nonansi() {
	let hir = compile_to_hir(parse("
		module test (input clk);
			output [7:0] data;
		endmodule
	"));
	let m = unwrap_single_module(&hir);

	// TODO: Verify that this fails for the right reason. Maybe look at the
	// diagnostics generated.
}
