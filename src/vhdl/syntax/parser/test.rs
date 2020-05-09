// Copyright (c) 2016-2020 Fabian Schuiki

use crate::ast;
use crate::lexer::token;
use crate::lexer::Lexer;
use crate::parser::basic::BasicParser;
use crate::parser::core::*;
use crate::parser::rules::*;
use moore_common::errors::*;
use moore_common::grind::{self, Grinder};
use moore_common::source::*;
use std::fmt::Debug;

macro_rules! parse {
    ($content:expr, $parse_fn:expr) => {{
        // Create an anonymous source file with the given content.
        let src = get_source_manager().add_anonymous($content);

        // Assemble a parser for the source.
        let content = src.get_content();
        let bytes = grind::from_iter(content.bytes().iter().map(|x| *x))
            .vent(|err: DiagBuilder2| eprintln!("{}", err));
        let tokens = Lexer::new(bytes, src);
        let mut parser = BasicParser::new(tokens);

        // Check the result.
        parse_impl(&mut parser, $parse_fn)
    }};
}

fn parse_impl<P, F, R, E>(p: &mut P, mut parse_fn: F) -> R
where
    P: Parser,
    F: FnMut(&mut P) -> Result<R, E>,
    E: Debug,
{
    // Apply the parser.
    let result = parse_fn(p).expect("parser failed");

    // Check whether the entire input has been consumed.
    match p.peek(0) {
        Spanned {
            value: token::Eof, ..
        } => (),
        Spanned { value, span } => {
            panic!(
                "{}",
                DiagBuilder2::error("Not entire input consumed").span(span.begin())
            );
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
    parse!("library ieee;", try_context_item);
}

#[test]
fn use_clause() {
    parse!("use ieee;", try_context_item);
    parse!("use ieee, ieee.std_logic_1164.all;", try_context_item);
    parse!("use work.'X', work.\"+\";", try_context_item);
}

#[test]
fn context_ref() {
    parse!("context ctx;", try_context_item);
    parse!("context ctx, work, stuff;", try_context_item);
    parse!("context work.'X', work'blah.text;", try_context_item);
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
    parse!(
        "
        context project_context is
            library project_lib;
            use project_lib.project_defs.all;
            library IP_lib;
            context IP_lib.IP_context;
        end context project_context;
    ",
        parse_context_decl
    );
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
    parse!(
        "
        entity Full_Adder is
            port (X, Y, Cin: in Bit; Cout, Sum: out Bit);
        end Full_Adder;
    ",
        parse_entity_decl
    );
    parse!(
        "
        entity AndGate is
            generic (N: Natural := 2);
            port (Inputs: in Bit_Vector (1 to N); Result: out Bit);
        end entity AndGate;
    ",
        parse_entity_decl
    );
    parse!(
        "
        entity TestBench is
        end TestBench;
    ",
        parse_entity_decl
    );
}

#[test]
fn entity_decl_part() {
    parse!(
        "
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
    ",
        parse_entity_decl
    );
}

#[test]
fn intf_decl() {
    parse!(
        "
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
    ",
        |p| separated_nonempty(
            p,
            token::Semicolon,
            token::Period,
            "interface declaration",
            |p| parse_intf_decl(p, None)
        )
    );

    // Default objects.
    parse!("a, b, c : in integer", |p| parse_intf_decl(
        p,
        Some(ast::IntfObjKind::Const)
    ));
    parse!("a, b, c : inout integer bus", |p| parse_intf_decl(
        p,
        Some(ast::IntfObjKind::Signal)
    ));
    parse!("a, b, c : inout integer", |p| parse_intf_decl(
        p,
        Some(ast::IntfObjKind::Var)
    ));
}

#[test]
fn subtype_ind() {
    parse!("integer", parse_subtype_ind);
    parse!("resfunc integer", parse_subtype_ind);
    parse!("(elemresfunc) integer", parse_subtype_ind);
    parse!(
        "(a resfunc, b resfunc, c (elemresfunc)) integer",
        parse_subtype_ind
    );
    parse!("integer range foo", parse_subtype_ind);
    parse!("integer range 1 to 8", parse_subtype_ind);
}

#[test]
fn elem_resolution() {
    parse!("(func)", parse_paren_expr);
    parse!("((elemfunc))", parse_paren_expr);
    parse!("((elemfunc) stuff (1 to 4))", parse_paren_expr);
    parse!(
        "(a func, b func, c (elemfunc), d (x elemfunc, y elemenfunc))",
        parse_paren_expr
    );
}

#[test]
fn package_inst() {
    parse!("package foo is new bar;", |p| parse_package_inst(p, true));
    parse!("package foo is new bar generic map (STUFF => 8);", |p| {
        parse_package_inst(p, true)
    });
}

#[test]
fn decl_items() {
    parse!(
        "
        package foo is
            -- package_{decl,body,inst}
            package bar is end;
            package body bar is end;
            package baz is new foo;
            package baz is new foo generic map (STUFF => 8);
        end;
    ",
        parse_package_decl
    );
}

#[test]
fn protected_type_decl() {
    parse!(
        "
        type SharedCounter is protected
            procedure increment (N: Integer := 1);
            procedure decrement (N: Integer := 1);
            impure function value return Integer;
        end protected SharedCounter;
    ",
        |p| parse_type_decl(p, true)
    );

    parse!(
        "
        type ComplexNumber is protected
            procedure extract (variable r, i: out Real);
            procedure add (variable a, b: inout ComplexNumber);
        end protected ComplexNumber;
    ",
        |p| parse_type_decl(p, true)
    );

    parse!(
        "
        type VariableSizeBitArray is protected
            procedure add_bit (index: Positive; value: Bit);
            impure function size return Natural;
        end protected VariableSizeBitArray;
    ",
        |p| parse_type_decl(p, true)
    );
}

#[test]
fn protected_type_body() {
    parse!(
        "
        type SharedCounter is protected body
            variable counter: Integer := 0;

            procedure increment (N: Integer := 1) is
            begin
                counter := counter + N;
            end procedure increment;

            procedure decrement (N: Integer := 1) is
            begin
                counter := counter - N;
            end procedure decrement;

            impure function value return Integer is
            begin
                return counter;
            end function value;
        end protected body SharedCounter;
    ",
        |p| parse_type_decl(p, true)
    );

    parse!(
        "
        type ComplexNumber is protected body
            variable re, im: Real;

            procedure extract (r, i: out Real) is
            begin
                r := re;
                i := im;
            end procedure extract;

            procedure add (variable a, b: inout ComplexNumber) is
                variable a_real, b_real: Real;
                variable a_imag, b_imag: Real;
            begin
                a.extract (a_real, a_imag);
                b.extract (b_real, b_imag);
                re := a_real + b_real;
                im := a_imag + b_imag;
            end procedure add;
        end protected body ComplexNumber;
    ",
        |p| parse_type_decl(p, true)
    );

    parse!(
        "
        type VariableSizeBitArray is protected body
            type bit_vector_access is access Bit_Vector;

            variable bit_array: bit_vector_access := null;
            variable bit_array_length: Natural := 0;

            procedure add_bit (index: Positive; value: Bit) is
                variable tmp: bit_vector_access;
            begin
                if index > bit_array_length then
                    tmp := bit_array;
                    bit_array := new bit_vector (1 to index);
                    if tmp /= null then
                        bit_array (1 to bit_array_length) := tmp.all;
                        deallocate (tmp);
                    end if;
                    bit_array_length := index;
                end if;
                bit_array (index) := value;
            end procedure add_bit;

            impure function size return Natural is
            begin
                return bit_array_length;
            end function size;
        end protected body VariableSizeBitArray;
    ",
        |p| parse_type_decl(p, true)
    );
}

#[test]
fn alias_decl() {
    parse!("alias SIGN: BIT is REAL_NUMBER (0);", parse_alias_decl);
    parse!(
        "alias MANTISSA: BIT_VECTOR (23 downto 0) is REAL_NUMBER (8 to 31);",
        parse_alias_decl
    );
    parse!(
        "alias EXPONENT: BIT_VECTOR (1 to 7) is REAL_NUMBER (1 to 7);",
        parse_alias_decl
    );
    parse!("alias STD_BIT is STD.STANDARD.BIT;", parse_alias_decl);
    // parse!("alias '0' is STD.STANDARD.'0' [return STD.STANDARD.BIT];", parse_alias_decl);
    // parse!("alias '1' is STD.STANDARD.'1' [return STD.STANDARD.BIT];", parse_alias_decl);
}

#[test]
fn object_decl() {
    parse!("constant TOLER: DISTANCE := 1.5 nm;", parse_object_decl);
    parse!("constant PI: REAL := 3.141592;", parse_object_decl);
    parse!("constant CYCLE_TIME: TIME := 100 ns;", parse_object_decl);
    parse!(
        "constant Propagation_Delay: DELAY_LENGTH;",
        parse_object_decl
    );

    parse!(
        "signal S: STANDARD.BIT_VECTOR (1 to 10);",
        parse_object_decl
    );
    parse!("signal CLK1, CLK2: TIME;", parse_object_decl);
    parse!(
        "signal OUTPUT: WIRED_OR MULTI_VALUED_LOGIC;",
        parse_object_decl
    );
    parse!("signal CLK1, CLK2: TIME register;", parse_object_decl);
    parse!("signal CLK1, CLK2: TIME bus;", parse_object_decl);
    parse!("signal CLK1, CLK2: TIME := 5 ps;", parse_object_decl);

    parse!(
        "variable INDEX: INTEGER range 0 to 99 := 0;",
        parse_object_decl
    );
    parse!("variable COUNT: POSITIVE;", parse_object_decl);
    parse!(
        "variable MEMORY: BIT_MATRIX (0 to 7, 0 to 1023);",
        parse_object_decl
    );
    parse!("shared variable Counter: SharedCounter;", parse_object_decl);
    parse!(
        "shared variable addend, augend, result: ComplexNumber;",
        parse_object_decl
    );
    parse!(
        "variable bit_stack: VariableSizeBitArray;",
        parse_object_decl
    );

    parse!("file F1: IntegerFile;", parse_object_decl);
    parse!("file F2: IntegerFile is \"test.dat\";", parse_object_decl);
    parse!(
        "file F3: IntegerFile open WRITE_MODE is \"test.dat\";",
        parse_object_decl
    );
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
fn discon_spec() {
    parse!("disconnect A : T after 0 ns;", parse_discon_spec);
    parse!("disconnect A,B,C : T after 800 ns;", parse_discon_spec);
    parse!("disconnect others : T after 20 ps;", parse_discon_spec);
    parse!("disconnect all : T after 0 ns;", parse_discon_spec);
}

#[test]
fn config_decl() {
    parse!(
        "
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
    ",
        parse_arch_body
    );

    parse!(
        "
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
    ",
        parse_config_decl
    );
}
