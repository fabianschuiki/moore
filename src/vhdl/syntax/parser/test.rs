// Copyright (c) 2017 Fabian Schuiki

use std::fmt::Debug;
use moore_common::errors::*;
use moore_common::source::*;
use moore_common::grind::{self, Grinder};
use syntax::lexer::Lexer;
use syntax::lexer::token;
use syntax::parser::rules::*;
use syntax::parser::core::*;
use syntax::parser::basic::BasicParser;

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
			-- assert Clk='1' or Clk'Delayed'Stable (PulseWidth);
			-- CheckTiming (Setup, Din, Load, Clk);
		end;
	", parse_entity_decl);
}

#[test]
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
		procedure foo (hello : INTEGER);
		procedure foo parameter (hello: INTEGER);

		function foo return integer;
		function \"+\" return integer;
		function foo return integer is bar;
		function foo return integer is <>;
		function foo (hello : INTEGER) return integer;
		function foo parameter (hello : INTEGER) return integer;
		pure function foo return integer;
		impure function foo return integer;

		package foo is new bar generic map (a => b, c => d);
		package foo is new bar generic map (<>);
		package foo is new bar generic map (default);
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

	parse!("
		package TimeConstants is
			constant tPLH: Time := 10 ns;
			constant tPHL: Time := 12 ns;
			constant tPLZ: Time := 7 ns;
			constant tPZL: Time := 8 ns;
			constant tPHZ: Time := 8 ns;
			constant tPZH: Time := 9 ns;
		end TimeConstants;
	", parse_package_decl);

	parse!("
		package TriState is
			type Tri is ('0', '1', 'Z', 'E');
			function BitVal (Value: Tri) return Bit;
			function TriVal (Value: Bit) return Tri;
			type TriVector is array (Natural range <>) of Tri;
			function Resolve (Sources: TriVector) return Tri;
		end package TriState;
	", parse_package_decl);
}

#[test]
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
			--	return Bits(Tri'Pos(Value));
			end;

			function TriVal (Value: Bit) return Tri is
			begin
			--	return Tri'Val(Bit'Pos(Value));
			end;

			function Resolve (Sources: TriVector) return Tri is
				variable V: Tri := 'Z';
			begin
			--	for i in Sources'Range loop
			--		if Sources(i) /= 'Z' then
			--			if V = 'Z' then
			--				V := Sources(i);
			--			else
			--				return 'E';
			--			end if;
			--		end if;
			--	end loop;
			--	return V;
			end;
		end package body TriState;
	", parse_package_body);
}

#[test]
fn package_inst() {
	parse!("package foo is new bar;", |p| parse_package_inst(p, true));
	parse!("package foo is new bar generic map (STUFF => 8);", |p| parse_package_inst(p, true));
}

#[test]
fn decl_items() {
	parse!("
		package foo is
			-- package_{decl,body,inst}
			package bar is end;
			package body bar is end;
			package baz is new foo;
			package baz is new foo generic map (STUFF => 8);
		end;
	", parse_package_decl)
}

#[test]
fn type_decl() {
	parse!("
		package foo is
			-- enum_type_def
			type foo;
			type MULTI_LEVEL_LOGIC is (LOW, HIGH, RISING, FALLING, AMBIGUOUS);
			type BIT is ('0','1');
			type SWITCH_LEVEL is ('0','1','X');

			-- integer_type_def
			type TWOS_COMPLEMENT_INTEGER is range -32768 to 32767;
			type BYTE_LENGTH_INTEGER is range 0 to 255;
			type WORD_INDEX is range 31 downto 0;

			-- floating_type_def
			type bubba is range -1E18 to 1E18;

			-- physical_type_def
			type DURATION is range -1E18 to 1E18
				units
					fs;
					ps    = 1000 fs;
					ns    = 1000 ps;
					us    = 1000 ns;
					ms    = 1000 us;
					sec   = 1000 ms;
					min   = 60 sec;
				end units;
			type DISTANCE is range 0 to 1E16
				units
					-- primary unit:
					Å;
					-- metric lengths:
					nm   = 10 Å;
					um   = 1000 nm;
					mm   = 1000 um;
					cm   = 10 mm;
					m    = 1000 mm;
					km   = 1000 m;
					-- English lengths:
					mil  = 254000 Å;
					inch = 1000 mil;
					ft   = 12 inch;
					yd   = 3 ft;
					fm   = 6 ft;
					mi   = 5280 ft;
					lg   = 3 mi;
				end units DISTANCE;

			-- array_type_def
			type MY_WORD is array (0 to 31) of BIT;
			type DATA_IN is array (7 downto 0) of FIVE_LEVEL_LOGIC;
			type MEMORY is array (INTEGER range <>) of MY_WORD;
			type SIGNED_FXPT is array (INTEGER range <>) of BIT;
			type SIGNED_FXPT_VECTOR is array (NATURAL range <>) of SIGNED_FXPT;
			type SIGNED_FXPT_5x4 is array (1 to 5, 1 to 4) of SIGNED_FXPT;
			type Word is array (NATURAL range <>) of BIT;
			type Memory is array (NATURAL range <>) of Word (31 downto 0);
			type E is array (NATURAL range <>) of INTEGER;
			type T is array (1 to 10) of E (1 to 0);

			-- record_type_def
			type DATE is record
					DAY : INTEGER range 1 to 31;
					MONTH : MONTH_NAME;
					YEAR : INTEGER range 0 to 4000;
				end record;
			type SIGNED_FXPT_COMPLEX is record
					RE : SIGNED_FXPT;
					IM : SIGNED_FXPT;
				end record;

			-- access_type_def
			type ADDRESS is access MEMORY;
			type BUFFER_PTR is access TEMP_BUFFER;

			-- file_type_def
			type A is file of STRING;
			type B is file of NATURAL;
		end;
	", parse_package_decl)
}

#[test]
fn protected_type_decl() {
	parse!("
		type SharedCounter is protected
			procedure increment (N: Integer := 1);
			procedure decrement (N: Integer := 1);
			impure function value return Integer;
		end protected SharedCounter;
	", |p| parse_type_decl(p, true));

	parse!("
		type ComplexNumber is protected
			procedure extract (variable r, i: out Real);
			procedure add (variable a, b: inout ComplexNumber);
		end protected ComplexNumber;
	", |p| parse_type_decl(p, true));

	parse!("
		type VariableSizeBitArray is protected
			procedure add_bit (index: Positive; value: Bit);
			impure function size return Natural;
		end protected VariableSizeBitArray;
	", |p| parse_type_decl(p, true));
}

#[test]
fn protected_type_body() {
	parse!("
		type SharedCounter is protected body
			variable counter: Integer := 0;

			procedure increment (N: Integer := 1) is
			begin
			-- 	counter := counter + N;
			end procedure increment;

			procedure decrement (N: Integer := 1) is
			begin
			-- 	counter := counter - N;
			end procedure decrement;

			impure function value return Integer is
			begin
			-- 	return counter;
			end function value;
		end protected body SharedCounter;
	", |p| parse_type_decl(p, true));

	parse!("
		type ComplexNumber is protected body
			variable re, im: Real;

			procedure extract (r, i: out Real) is
			begin
			-- 	r := re;
			-- 	i := im;
			end procedure extract;

			procedure add (variable a, b: inout ComplexNumber) is
				variable a_real, b_real: Real;
				variable a_imag, b_imag: Real;
			begin
			-- 	a.extract (a_real, a_imag);
			-- 	b.extract (b_real, b_imag);
			-- 	re := a_real + b_real;
			-- 	im := a_imag + b_imag;
			end procedure add;
		end protected body ComplexNumber;
	", |p| parse_type_decl(p, true));

	parse!("
		type VariableSizeBitArray is protected body
			type bit_vector_access is access Bit_Vector;

			variable bit_array: bit_vector_access := null;
			variable bit_array_length: Natural := 0;

			procedure add_bit (index: Positive; value: Bit) is
				variable tmp: bit_vector_access;
			begin
			-- 	if index > bit_array_length then
			-- 		tmp := bit_array;
			-- 		bit_array := new bit_vector (1 to index);
			-- 		if tmp /= null then
			-- 			bit_array (1 to bit_array_length) := tmp.all;
			-- 			deallocate (tmp);
			-- 		end if;
			-- 		bit_array_length := index;
			-- 	end if;
			-- 	bit_array (index) := value;
			end procedure add_bit;

			impure function size return Natural is
			begin
			-- 	return bit_array_length;
			end function size;
		end protected body VariableSizeBitArray;
	", |p| parse_type_decl(p, true));
}

#[test]
fn alias_decl() {
	parse!("alias SIGN: BIT is REAL_NUMBER (0);", parse_alias_decl);
	parse!("alias MANTISSA: BIT_VECTOR (23 downto 0) is REAL_NUMBER (8 to 31);", parse_alias_decl);
	parse!("alias EXPONENT: BIT_VECTOR (1 to 7) is REAL_NUMBER (1 to 7);", parse_alias_decl);
	parse!("alias STD_BIT is STD.STANDARD.BIT;", parse_alias_decl);
	// parse!("alias '0' is STD.STANDARD.'0' [return STD.STANDARD.BIT];", parse_alias_decl);
	// parse!("alias '1' is STD.STANDARD.'1' [return STD.STANDARD.BIT];", parse_alias_decl);
}

#[test]
fn object_decl() {
	parse!("constant TOLER: DISTANCE := 1.5 nm;", parse_object_decl);
	parse!("constant PI: REAL := 3.141592;", parse_object_decl);
	parse!("constant CYCLE_TIME: TIME := 100 ns;", parse_object_decl);
	parse!("constant Propagation_Delay: DELAY_LENGTH;", parse_object_decl);

	parse!("signal S: STANDARD.BIT_VECTOR (1 to 10);", parse_object_decl);
	parse!("signal CLK1, CLK2: TIME;", parse_object_decl);
	parse!("signal OUTPUT: WIRED_OR MULTI_VALUED_LOGIC;", parse_object_decl);
	parse!("signal CLK1, CLK2: TIME register;", parse_object_decl);
	parse!("signal CLK1, CLK2: TIME bus;", parse_object_decl);
	parse!("signal CLK1, CLK2: TIME := 5 ps;", parse_object_decl);

	parse!("variable INDEX: INTEGER range 0 to 99 := 0;", parse_object_decl);
	parse!("variable COUNT: POSITIVE;", parse_object_decl);
	parse!("variable MEMORY: BIT_MATRIX (0 to 7, 0 to 1023);", parse_object_decl);
	parse!("shared variable Counter: SharedCounter;", parse_object_decl);
	parse!("shared variable addend, augend, result: ComplexNumber;", parse_object_decl);
	parse!("variable bit_stack: VariableSizeBitArray;", parse_object_decl);

	parse!("file F1: IntegerFile;", parse_object_decl);
	parse!("file F2: IntegerFile is \"test.dat\";", parse_object_decl);
	parse!("file F3: IntegerFile open WRITE_MODE is \"test.dat\";", parse_object_decl);
}

#[test]
fn expr() {
	parse!("null", parse_expr);
	parse!("open", parse_expr);
	parse!("others", parse_expr);
}

#[test]
fn subtype_decl() {
	parse!("subtype foo is integer;", parse_subtype_decl);
}

#[test]
fn arch_body() {
	parse!("
		architecture DataFlow of Full_Adder is
			signal A,B: Bit;
		begin
			-- A <= X xor Y;
			-- B <= A and Cin;
			-- Sum <= A xor Cin;
			-- Cout <= B or (X and Y);
		end architecture DataFlow;
	", parse_arch_body);

	parse!("
		architecture Structure of TestBench is
			component C is end component C;
			component Full_Adder
				port (X, Y, Cin: Bit; Cout, Sum: out Bit);
			end component;
			signal A,B,C,D,E,F,G: Bit;
			signal OK: Boolean;
		begin
			-- UUT:        Full_Adder port map (A,B,C,D,E);
			-- Generator:  AdderTest  port map (A,B,C,F,G);
			-- Comparator: AdderCheck port map (D,E,F,G,OK);
		end Structure;
	", parse_arch_body);

	parse!("
		architecture Behavior of AndGate is begin
			-- process (Inputs)
			-- 	variable Temp: Bit;
			-- begin
			-- 	Temp := '1';
			-- 	for i in Inputs'Range loop
			-- 		if Inputs(i) = '0' then
			-- 			Temp := '0';
			-- 			exit;
			-- 		end if;
			-- 	end loop;
			-- 	Result <= Temp after 10 ns;
			-- end process;
		end Behavior;
	", parse_arch_body);
}

#[test]
fn discon_spec() {
	parse!("disconnect A : T after 0 ns;", parse_discon_spec);
	parse!("disconnect A,B,C : T after 800 ns;", parse_discon_spec);
	parse!("disconnect others : T after 20 ps;", parse_discon_spec);
	parse!("disconnect all : T after 0 ns;", parse_discon_spec);
}

#[test]
fn config_decl() {
	parse!("
		architecture Structure of Half_Adder is
			for L1: XOR_GATE use
				entity WORK.XOR_GATE(Behavior)
					generic map (3 ns, 3 ns)
					port map (I1 => I1, I2 => I2, O => O);
			for L2: AND_GATE use
				entity WORK.AND_GATE(Behavior)
					generic map (3 ns, 4 ns)
					port map (I1, open, O);
		begin
		end architecture Structure;
	", parse_arch_body);

	parse!("
		configuration Different of Half_Adder is
			for Structure
				for L1: XOR_GATE
					generic map (2.9 ns, 3.6 ns);
				end for;
				for L2: AND_GATE
					generic map (2.8 ns, 3.25 ns)
					port map (I2 => Tied_High);
				end for;
			end for;
		end configuration Different;
	", parse_config_decl);
}
