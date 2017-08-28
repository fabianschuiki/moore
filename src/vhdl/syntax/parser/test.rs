// Copyright (c) 2017 Fabian Schuiki

use std::fmt::Debug;
use moore_common::errors::*;
use moore_common::name::*;
use moore_common::source::*;
use moore_common::grind::{self, Grinder};
use syntax::lexer::Lexer;
use syntax::lexer::token;
use syntax::parser::rules::*;
use syntax::parser::core::*;
use syntax::parser::basic::BasicParser;
use syntax::ast;

macro_rules! parse {
    ($content:expr, $parse_fn:expr) => {{
		// Create an anonymous source file with the given content.
		let src = get_source_manager().add_anonymous($content);

		// Assemble a parser for the source.
		let content = src.get_content();
		let bytes = grind::from_iter(content.bytes().iter().map(|x| *x))
			.vent(|err: DiagBuilder2| println!("{}", err));
		let tokens = Lexer::new(bytes, src);
		let mut parser = BasicParser::new(tokens);

		// Check the result.
		parse_impl(&mut parser, $parse_fn)
    }}
}

fn parse_impl<P,F,R,E>(p: &mut P, mut parse_fn: F) -> R where
	P: Parser,
	F: FnMut(&mut P) -> Result<R,E>,
	E: Debug {

	// Apply the parser.
	let result = parse_fn(p).expect("parser failed");

	// Check whether the entire input has been consumed.
	match p.peek(0) {
		Spanned{ value: token::Eof, .. } => (),
		Spanned{ value, span } => {
			panic!("{}", DiagBuilder2::error("Not entire input consumed").span(span.begin()));
		}
	}

	result
}


#[test]
fn name() {
	parse!("simple", parse_name);
	parse!("'x'", parse_name);
	parse!("\"add\"", parse_name);
	parse!("simple.simple", parse_name);
	parse!("simple.'x'", parse_name);
	parse!("simple.\"add\"", parse_name);
	parse!("simple.all", parse_name);
	parse!("simple'attr", parse_name);
	// parse!("simple[ signature goes here ]'attr", parse_name);
	parse!("simple(1)", parse_name);
	parse!("simple(1,2)", parse_name);
	parse!("simple(1 to 2)", parse_name);
	parse!("simple(2 downto 1)", parse_name);
	parse!("simple range 2 downto 1", parse_name);
	parse!("simple range 1 to 42", parse_name);
}

#[test]
fn library_clause() {
	parse!("library ieee;", parse_context_item);
}

#[test]
fn use_clause() {
	parse!("use ieee;", parse_context_item);
	parse!("use ieee, ieee.std_logic_1164.all;", parse_context_item);
	parse!("use work.'X', work.\"+\";", parse_context_item);
}

#[test]
fn context_ref() {
	parse!("context ctx;", parse_context_item);
	parse!("context ctx, work, stuff;", parse_context_item);
	parse!("context work.'X', work'blah.text;", parse_context_item);
}

#[test]
fn design_unit() {
	parse!("entity foo is end;", parse_design_unit);
	// parse!("configuration foo is begin end;", parse_design_unit);
	parse!("package foo is end;", parse_design_unit);
	parse!("context foo is end;", parse_design_unit);
}

#[test]
fn context_decl() {
	parse!("context foo is end;", parse_context_decl);
	parse!("context foo is end context;", parse_context_decl);
	parse!("context foo is end context foo;", parse_context_decl);
	// parse!("context foo is end context bar;", parse_context_decl); // check if this emits a warning
	parse!("
		context project_context is
			library project_lib;
			use project_lib.project_defs.all;
			library IP_lib;
			context IP_lib.IP_context;
		end context project_context;
	", parse_context_decl);
}

#[test]
fn entity_decl() {
	parse!("entity foo is end;", parse_entity_decl);
	parse!("entity foo is end entity;", parse_entity_decl);
	parse!("entity foo is end entity foo;", parse_entity_decl);
	// parse!("entity foo is end entity bar;", parse_entity_decl); // check if this emits a warning
	parse!("entity foo is begin end;", parse_entity_decl);
}

#[test]
fn entity_header() {
	parse!("
		entity Full_Adder is
			port (X, Y, Cin: in Bit; Cout, Sum: out Bit);
		end Full_Adder;
	", parse_entity_decl);
	parse!("
		entity AndGate is
			generic (N: Natural := 2);
			port (Inputs: in Bit_Vector (1 to N); Result: out Bit);
		end entity AndGate;
	", parse_entity_decl);
	parse!("
		entity TestBench is
		end TestBench;
	", parse_entity_decl);
}

#[test]
#[ignore]
fn entity_decl_part() {
	parse!("
		entity ROM is
			port (
				Addr: in Word;
				Data: out Word;
				Sel: in Bit);
			type Instruction is array (1 to 5) of Natural;
			type Program is array (Natural range <>) of Instruction;
			use Work.OpCodes.all, Work.RegisterNames.all;
			constant ROM_Code: Program := (
				(STM, R14, R12, 12, R13),
				(LD,  R7,  32,  0,  R1 ),
				(BAL, R14, 0,   0,  R7 )
			);
		end ROM;
	", parse_entity_decl);
}

#[test]
#[ignore]
fn entity_stmt_part() {
	parse!("
		entity Latch is
			port (
				Din: in Word;
				Dout: out Word;
				Load: in Bit;
				Clk: in Bit);
			constant Setup: Time := 12 ns;
			constant PulseWidth: Time := 50 ns;
			use Work.TimingMonitors.all;
		begin
			assert Clk='1' or Clk'Delayed'Stable (PulseWidth);
			CheckTiming (Setup, Din, Load, Clk);
		end;
	", parse_entity_decl);
}

#[test]
#[ignore]
fn intf_decl() {
	parse!("
		constant a : std_logic;
		constant a, b, c : in std_logic;
		constant a, b, c : in std_logic := '0';

		signal a : std_logic;
		signal a, b, c : in std_logic;
		signal a, b, c : out std_logic;
		signal a, b, c : inout std_logic;
		signal a, b, c : buffer std_logic;
		signal a, b, c : linkage std_logic;
		signal a, b, c : in std_logic bus;
		signal a, b, c : in std_logic bus := '0';

		variable a : std_logic;
		variable a, b, c : in std_logic;
		variable a, b, c : out std_logic;
		variable a, b, c : inout std_logic;
		variable a, b, c : buffer std_logic;
		variable a, b, c : linkage std_logic;
		variable a, b, c : in std_logic := '0';

		file i : integer;
		type foo;

		procedure foo;
		procedure \"+\";
		procedure foo is bar;
		procedure foo is <>;
		procedure foo ();
		procedure foo parameter ();

		function foo return integer;
		function \"+\" return integer;
		function foo return integer is bar;
		function foo return integer is <>;
		function foo () return integer;
		function foo parameter () return integer;
		pure function foo return integer;
		impure function foo return integer;

		package foo is new bar generic map (a => b, c => d);
		package foo is new bar generic map (<>);
		package foo is new bar generic map (default).
	", |p| separated_nonempty(p,
		token::Semicolon,
		token::Period,
		"interface declaration",
		|p| parse_intf_decl(p, None)
	));

	// Default objects.
	parse!("a, b, c : in integer", |p| parse_intf_decl(p, Some(IntfObjectKind::Constant)));
	parse!("a, b, c : inout integer bus", |p| parse_intf_decl(p, Some(IntfObjectKind::Signal)));
	parse!("a, b, c : inout integer", |p| parse_intf_decl(p, Some(IntfObjectKind::Variable)));
}

#[test]
fn subtype_ind() {
	parse!("integer", parse_subtype_ind);
	parse!("resfunc integer", parse_subtype_ind);
	parse!("(elemresfunc) integer", parse_subtype_ind);
	parse!("(a resfunc, b resfunc, c (elemresfunc)) integer", parse_subtype_ind);
	parse!("integer range foo", parse_subtype_ind);
	parse!("integer range 1 to 8", parse_subtype_ind);
}

#[test]
fn elem_resolution() {
	parse!("(func)", |p| flanked(p, token::Paren, parse_paren_expr));
	parse!("((elemfunc))", |p| flanked(p, token::Paren, parse_paren_expr));
	parse!("((elemfunc) stuff (1 to 4))", |p| flanked(p, token::Paren, parse_paren_expr));
	parse!("(a func, b func, c (elemfunc), d (x elemfunc, y elemenfunc))", |p| flanked(p, token::Paren, parse_paren_expr));
}

#[test]
fn package_decl() {
	parse!("package foo is end;", parse_package_decl);
	parse!("package foo is end package;", parse_package_decl);
	parse!("package foo is end package foo;", parse_package_decl);
	// parse!("package foo is end package bar;", parse_package_decl); // check if this emits a warning

	parse!("
		package foo is
			generic (stuff : INTEGER := 0);
		end;
	", parse_package_decl);

	parse!("
		package foo is
			generic (stuff : INTEGER := 0);
			generic map (stuff => 0);
		end;
	", parse_package_decl);

	// parse!("
	// 	package TimeConstants is
	// 		constant tPLH: Time := 10 ns;
	// 		constant tPHL: Time := 12 ns;
	// 		constant tPLZ: Time := 7 ns;
	// 		constant tPZL: Time := 8 ns;
	// 		constant tPHZ: Time := 8 ns;
	// 		constant tPZH: Time := 9 ns;
	// 	end TimeConstants;
	// ", parse_package_decl);

	// parse!("
	// 	package TriState is
	// 		type Tri is ('0', '1', 'Z', 'E');
	// 		function BitVal (Value: Tri) return Bit;
	// 		function TriVal (Value: Bit) return Tri;
	// 		type TriVector is array (Natural range <>) of Tri;
	// 		function Resolve (Sources: TriVector) return Tri;
	// 	end package TriState;
	// ", parse_package_decl);
}

#[test]
#[ignore]
fn package_body() {
	parse!("package body foo is end;", parse_package_body);
	parse!("package body foo is end package body;", parse_package_body);
	parse!("package body foo is end package body foo;", parse_package_body);
	// parse!("package body foo is end package body bar;", parse_package_body); // check if this emits a warning

	parse!("
		package body TriState is
			function BitVal (Value: Tri) return Bit is
				constant Bits : Bit_Vector := \"0100\";
			begin
				return Bits(Tri'Pos(Value));
			end;

			function TriVal (Value: Bit) return Tri is
			begin
				return Tri'Val(Bit'Pos(Value));
			end;

			function Resolve (Sources: TriVector) return Tri is
				variable V: Tri := 'Z';
			begin
				for i in Sources'Range loop
					if Sources(i) /= 'Z' then
						if V = 'Z' then
							V := Sources(i);
						else
							return 'E';
						end if;
					end if;
				end loop;
				return V;
			end;
		end package body TriState;
	", parse_package_body);
}

#[test]
fn package_inst() {
	parse!("package foo is new bar;", parse_package_inst);
	parse!("package foo is new bar generic map (STUFF => 8);", parse_package_inst);
}
