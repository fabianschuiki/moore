// Copyright (c) 2017 Fabian Schuiki

//! A VHDL lexer. This module implements lexical analysis of VHDL source files.
//! It converts a stream of input bytes into a stream of language tokens such as
//! identifiers, literals, and symbols.

pub mod categorizer;
pub mod bundler;
pub mod tokenizer;
pub mod token;

use moore_common::grind::Grinder;
use moore_common::grind::utf8::Utf8;
use moore_common::errors::*;
use moore_common::source::*;
use self::bundler::Bundler;
use self::categorizer::Categorizer;
use self::tokenizer::Tokenizer;
use self::token::*;


/// A VHDL lexer. Converts a stream of bytes to VHDL tokens. Emits errors
/// backwards up the pipeline.
pub struct Lexer<T: Grinder<Item=Option<u8>, Error=DiagBuilder2>> {
	inner: Tokenizer<Bundler<Categorizer<Utf8<T>>>>,
}

impl<T> Lexer<T> where T: Grinder<Item=Option<u8>, Error=DiagBuilder2> {
	/// Create a new lexer.
	pub fn new(bytes: T, src: Source) -> Lexer<T> {
		let chars = Utf8::new(bytes);
		let cat = Categorizer::new(chars);
		let bundles = Bundler::new(cat, src);
		let tokens = Tokenizer::new(bundles);
		Lexer { inner: tokens }
	}
}

impl<T> Grinder for Lexer<T> where T: Grinder<Item=Option<u8>, Error=DiagBuilder2> {
	type Item = Option<Spanned<Token>>;
	type Error = DiagBuilder2;

	fn next(&mut self) -> Self::Item {
		self.inner.next()
	}

	fn emit(&mut self, err: Self::Error) {
		self.inner.emit(err)
	}
}



#[cfg(test)]
mod test {
	use super::Lexer;
	use moore_common::source::*;
	use moore_common::name::*;
	use moore_common::errors::*;
	use moore_common::grind::{self, Grinder};
	use syntax::lexer::token::*;

	fn lex(src: Source) -> Vec<Token> {
		let content = src.get_content();
		let bytes = grind::from_iter(content.bytes().iter().map(|x| *x))
			.vent(|err: DiagBuilder2| println!("{}", err));
		let mut tokens = Lexer::new(bytes, src);
		let mut v = Vec::new();
		while let Some(Spanned{ value, .. }) = tokens.next() {
			v.push(value);
		}
		v
	}

	fn check(input: &str, expected: &[Token]) {
		use std::cell::Cell;
		thread_local!(static INDEX: Cell<usize> = Cell::new(0));
		let sm = get_source_manager();
		let idx = INDEX.with(|i| {
			let v = i.get();
			i.set(v+1);
			v
		});
		let source = sm.add(&format!("test_{}.vhd", idx), input);
		let actual = lex(source);
		assert_eq!(actual.len(), expected.len());
		for (a,&e) in actual.into_iter().zip(expected.into_iter()) {
			assert_eq!(a, e);
		}
	}

	fn name(n: &str) -> Name {
		get_name_table().intern(n, false)
	}

	fn name_case(n: &str) -> Name {
		get_name_table().intern(n, true)
	}

	#[test]
	fn basic_ident() {
		check(r"
			COUNT    X     c_out        FFT                Decoder
			VHSIC    X1    PageCount    STORE_NEXT_ITEM    As49__8
		", &[
			Ident(name("COUNT")),
			Ident(name("X")),
			Ident(name("c_out")),
			Ident(name("FFT")),
			Ident(name("Decoder")),
			Ident(name("VHSIC")),
			Ident(name("X1")),
			Ident(name("PageCount")),
			Ident(name("STORE_NEXT_ITEM")),
			Ident(name("As49__8")),
		]);
	}

	#[test]
	fn extended_ident() {
		check(r"
			-- Two different identifiers, neither of which is the reserved word bus.
			\BUS\  \bus\

			-- An identifier containing three characters.
			\a\\b\

			-- Three distinct identifiers.
			VHDL  \VHDL\  \vhdl\

			-- Use of spaces and special characters.
			\A B\  \!@#\  \_+`'''1#{}\
		", &[
			Ident(name_case("\\BUS\\")),
			Ident(name_case("\\bus\\")),
			Ident(name_case("\\a\\b\\")),
			Ident(name("VHDL")),
			Ident(name_case("\\VHDL\\")),
			Ident(name_case("\\vhdl\\")),
			Ident(name_case("\\A B\\")),
			Ident(name_case("\\!@#\\")),
			Ident(name_case("\\_+`'''1#{}\\")),
		]);
	}

	#[test]
	fn decimal_literal() {
		check(r"
			12         0        1E6         123_456      -- Integer literals.
			12.0       0.0      0.456       3.14159_26   -- Real literals.
			1.34E-12   1.0E+6   6.023E+24                -- Real literals with exponents.
		", &[
			Lit(Literal::Abstract(None, name_case("12"), None, None)),
			Lit(Literal::Abstract(None, name_case("0"), None, None)),
			Lit(Literal::Abstract(None, name_case("1"), None, Some(Exponent(ExponentSign::Positive, name_case("6"))))),
			Lit(Literal::Abstract(None, name_case("123456"), None, None)),
			Lit(Literal::Abstract(None, name_case("12"), Some(name_case("0")), None)),
			Lit(Literal::Abstract(None, name_case("0"), Some(name_case("0")), None)),
			Lit(Literal::Abstract(None, name_case("0"), Some(name_case("456")), None)),
			Lit(Literal::Abstract(None, name_case("3"), Some(name_case("1415926")), None)),
			Lit(Literal::Abstract(None, name_case("1"), Some(name_case("34")), Some(Exponent(ExponentSign::Negative, name_case("12"))))),
			Lit(Literal::Abstract(None, name_case("1"), Some(name_case("0")), Some(Exponent(ExponentSign::Positive, name_case("6"))))),
			Lit(Literal::Abstract(None, name_case("6"), Some(name_case("023")), Some(Exponent(ExponentSign::Positive, name_case("24"))))),
		]);
	}

	#[test]
	fn based_literal() {
		check(r"
			2#1111_1111#   16#FF#   016#0FF#       -- Integer literals of value 255
			16#E#E1        2#1110_0000#            -- Integer literals of value 224
			16#F.FF#E+2    2#1.1111_1111_111#E11   -- Real literals of value 4095.0
		", &[
			Lit(Literal::Abstract(Some(name_case("2")), name_case("11111111"), None, None)),
			Lit(Literal::Abstract(Some(name_case("16")), name_case("FF"), None, None)),
			Lit(Literal::Abstract(Some(name_case("016")), name_case("0FF"), None, None)),
			Lit(Literal::Abstract(Some(name_case("16")), name_case("E"), None, Some(Exponent(ExponentSign::Positive, name_case("1"))))),
			Lit(Literal::Abstract(Some(name_case("2")), name_case("11100000"), None, None)),
			Lit(Literal::Abstract(Some(name_case("16")), name_case("F"), Some(name_case("FF")), Some(Exponent(ExponentSign::Positive, name_case("2"))))),
			Lit(Literal::Abstract(Some(name_case("2")), name_case("1"), Some(name_case("11111111111")), Some(Exponent(ExponentSign::Positive, name_case("11"))))),
		]);
	}

	#[test]
	fn bit_string_literal() {
		check("
			B\"1111_1111_1111\"  -- Equivalent to the string literal \"111111111111\".
			X\"FFF\"             -- Equivalent to B\"1111_1111_1111\".
			O\"777\"             -- Equivalent to B\"111_111_111\".
			X\"777\"             -- Equivalent to B\"0111_0111_0111\".

			B\"XXXX_01LH\"       -- Equivalent to the string literal \"XXXX01LH\"
			UO\"27\"             -- Equivalent to B\"010_111\"
			UO\"2C\"             -- Equivalent to B\"011_CCC\"
			SX\"3W\"             -- Equivalent to B\"0011_WWWW\"
			D\"35\"              -- Equivalent to B\"100011\"

			12UB\"X1\"           -- Equivalent to B\"0000_0000_00X1\"
			12SB\"X1\"           -- Equivalent to B\"XXXX_XXXX_XXX1\"
			12UX\"F-\"           -- Equivalent to B\"0000_1111_----\"
			12SX\"F-\"           -- Equivalent to B\"1111_1111_----\"
			12D\"13\"            -- Equivalent to B\"0000_0000_1101\"

			12UX\"000WWW\"       -- Equivalent to B\"WWWW_WWWW_WWWW\"
			12SX\"FFFC00\"       -- Equivalent to B\"1100_0000_0000\"
			12SX\"XXXX00\"       -- Equivalent to B\"XXXX_0000_0000\"
		", &[
			Lit(Literal::BitString(None, BitStringBase::B, name_case("111111111111"))),
			Lit(Literal::BitString(None, BitStringBase::X, name_case("FFF"))),
			Lit(Literal::BitString(None, BitStringBase::O, name_case("777"))),
			Lit(Literal::BitString(None, BitStringBase::X, name_case("777"))),

			Lit(Literal::BitString(None, BitStringBase::B, name_case("XXXX01LH"))),
			Lit(Literal::BitString(None, BitStringBase::UO, name_case("27"))),
			Lit(Literal::BitString(None, BitStringBase::UO, name_case("2C"))),
			Lit(Literal::BitString(None, BitStringBase::SX, name_case("3W"))),
			Lit(Literal::BitString(None, BitStringBase::D, name_case("35"))),

			Lit(Literal::BitString(Some(name_case("12")), BitStringBase::UB, name_case("X1"))),
			Lit(Literal::BitString(Some(name_case("12")), BitStringBase::SB, name_case("X1"))),
			Lit(Literal::BitString(Some(name_case("12")), BitStringBase::UX, name_case("F-"))),
			Lit(Literal::BitString(Some(name_case("12")), BitStringBase::SX, name_case("F-"))),
			Lit(Literal::BitString(Some(name_case("12")), BitStringBase::D, name_case("13"))),

			Lit(Literal::BitString(Some(name_case("12")), BitStringBase::UX, name_case("000WWW"))),
			Lit(Literal::BitString(Some(name_case("12")), BitStringBase::SX, name_case("FFFC00"))),
			Lit(Literal::BitString(Some(name_case("12")), BitStringBase::SX, name_case("XXXX00"))),
		]);
	}

	#[test]
	fn character_literal() {
		check("
			'A'  '*'  '''  ' '
		", &[
			Lit(Literal::Char('A')),
			Lit(Literal::Char('*')),
			Lit(Literal::Char('\'')),
			Lit(Literal::Char(' ')),
		]);
	}

	#[test]
	fn string_literal() {
		check("
			\"Setup time is too short\"  --  An error message.
			\"\"                         --  An empty string literal.
			\" \"   \"A\"   \"\"\"\"     --  Three string literals of length 1.
			\"Characters such as $, %, and } are allowed in string literals.\"
		", &[
			Lit(Literal::String(name_case("Setup time is too short"))),
			Lit(Literal::String(name_case(""))),
			Lit(Literal::String(name_case(" "))),
			Lit(Literal::String(name_case("A"))),
			Lit(Literal::String(name_case("\""))),
			Lit(Literal::String(name_case("Characters such as $, %, and } are allowed in string literals."))),
		]);
	}

	#[test]
	fn symbols() {
		check("
			(    )
			.    ,    :    ;    '    &
			=>   ??   <>   :=   <<   >>
			=    /=   <    <=   >    >=
			?=   ?/=  ?<   ?<=  ?>   ?>=
			+    -    *    /    **
		", &[
			OpenDelim(Paren),
			CloseDelim(Paren),

			Period,
			Comma,
			Colon,
			Semicolon,
			Apostrophe,
			Ampersand,

			Arrow,
			Condition,
			LtGt,
			VarAssign,
			Lshift,
			Rshift,

			Eq,
			Neq,
			Lt,
			Leq,
			Gt,
			Geq,

			MatchEq,
			MatchNeq,
			MatchLt,
			MatchLeq,
			MatchGt,
			MatchGeq,

			Add,
			Sub,
			Mul,
			Div,
			Pow,
		]);
	}

	#[test]
	fn keywords() {
		check("
			abs access after alias all and architecture array assert assume
			assume_guarantee attribute begin block body buffer bus case
			component configuration constant context cover default disconnect
			downto else elsif end entity exit fairness file for force function
			generate generic group guarded if impure in inertial inout is label
			library linkage literal loop map mod nand new next nor not null of
			on open or others out package parameter port postponed procedure
			process property protected pure range record register reject release
			rem report restrict restrict_guarantee return rol ror select
			sequence severity shared signal sla sll sra srl strong subtype then
			to transport type unaffected units until use variable vmode vprop
			vunit wait when while with xnor xor
		", &[
			Keyword(Kw::Abs),
			Keyword(Kw::Access),
			Keyword(Kw::After),
			Keyword(Kw::Alias),
			Keyword(Kw::All),
			Keyword(Kw::And),
			Keyword(Kw::Architecture),
			Keyword(Kw::Array),
			Keyword(Kw::Assert),
			Keyword(Kw::Assume),
			Keyword(Kw::AssumeGuarantee),
			Keyword(Kw::Attribute),
			Keyword(Kw::Begin),
			Keyword(Kw::Block),
			Keyword(Kw::Body),
			Keyword(Kw::Buffer),
			Keyword(Kw::Bus),
			Keyword(Kw::Case),
			Keyword(Kw::Component),
			Keyword(Kw::Configuration),
			Keyword(Kw::Constant),
			Keyword(Kw::Context),
			Keyword(Kw::Cover),
			Keyword(Kw::Default),
			Keyword(Kw::Disconnect),
			Keyword(Kw::Downto),
			Keyword(Kw::Else),
			Keyword(Kw::Elsif),
			Keyword(Kw::End),
			Keyword(Kw::Entity),
			Keyword(Kw::Exit),
			Keyword(Kw::Fairness),
			Keyword(Kw::File),
			Keyword(Kw::For),
			Keyword(Kw::Force),
			Keyword(Kw::Function),
			Keyword(Kw::Generate),
			Keyword(Kw::Generic),
			Keyword(Kw::Group),
			Keyword(Kw::Guarded),
			Keyword(Kw::If),
			Keyword(Kw::Impure),
			Keyword(Kw::In),
			Keyword(Kw::Inertial),
			Keyword(Kw::Inout),
			Keyword(Kw::Is),
			Keyword(Kw::Label),
			Keyword(Kw::Library),
			Keyword(Kw::Linkage),
			Keyword(Kw::Literal),
			Keyword(Kw::Loop),
			Keyword(Kw::Map),
			Keyword(Kw::Mod),
			Keyword(Kw::Nand),
			Keyword(Kw::New),
			Keyword(Kw::Next),
			Keyword(Kw::Nor),
			Keyword(Kw::Not),
			Keyword(Kw::Null),
			Keyword(Kw::Of),
			Keyword(Kw::On),
			Keyword(Kw::Open),
			Keyword(Kw::Or),
			Keyword(Kw::Others),
			Keyword(Kw::Out),
			Keyword(Kw::Package),
			Keyword(Kw::Parameter),
			Keyword(Kw::Port),
			Keyword(Kw::Postponed),
			Keyword(Kw::Procedure),
			Keyword(Kw::Process),
			Keyword(Kw::Property),
			Keyword(Kw::Protected),
			Keyword(Kw::Pure),
			Keyword(Kw::Range),
			Keyword(Kw::Record),
			Keyword(Kw::Register),
			Keyword(Kw::Reject),
			Keyword(Kw::Release),
			Keyword(Kw::Rem),
			Keyword(Kw::Report),
			Keyword(Kw::Restrict),
			Keyword(Kw::RestrictGuarantee),
			Keyword(Kw::Return),
			Keyword(Kw::Rol),
			Keyword(Kw::Ror),
			Keyword(Kw::Select),
			Keyword(Kw::Sequence),
			Keyword(Kw::Severity),
			Keyword(Kw::Shared),
			Keyword(Kw::Signal),
			Keyword(Kw::Sla),
			Keyword(Kw::Sll),
			Keyword(Kw::Sra),
			Keyword(Kw::Srl),
			Keyword(Kw::Strong),
			Keyword(Kw::Subtype),
			Keyword(Kw::Then),
			Keyword(Kw::To),
			Keyword(Kw::Transport),
			Keyword(Kw::Type),
			Keyword(Kw::Unaffected),
			Keyword(Kw::Units),
			Keyword(Kw::Until),
			Keyword(Kw::Use),
			Keyword(Kw::Variable),
			Keyword(Kw::Vmode),
			Keyword(Kw::Vprop),
			Keyword(Kw::Vunit),
			Keyword(Kw::Wait),
			Keyword(Kw::When),
			Keyword(Kw::While),
			Keyword(Kw::With),
			Keyword(Kw::Xnor),
			Keyword(Kw::Xor),
		]);
	}
}
