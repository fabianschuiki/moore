// Copyright (c) 2016 Fabian Schuiki

//! Defines all tokens that may result from performing lexical analysis on a
//! VHDL source file. This module is inspired heavily by the tokens used in the
//! Rust compiler.

pub use self::DelimToken::*;
pub use self::Lit::*;
pub use self::Token::*;
use name::{Name, NameTable};


/// A primary token emitted by the Lexer.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Token {
	// Symbols
	Ampersand,
	Apostrophe,
	Arrow,
	Colon,
	ColonEq,
	Comma,
	Equal,
	Gt,
	GtEq,
	Lt,
	LtEq,
	LtGt,
	Minus,
	Period,
	Pipe,
	Plus,
	Semicolon,
	Slash,
	SlashEq,
	Star,
	StarStar,

	/// An opening delimiter
	OpenDelim(DelimToken),
	/// A closing delimiter
	CloseDelim(DelimToken),

	/// A literal
	Literal(Lit),

	/// An identifier
	Ident(Name),

	/// The end of the input file
	Eof,
}

impl Token {
	/// Check if the token is the given keyword.
	pub fn is_keyword(&self, kw: Name) -> bool {
		match *self {
			Ident(name) => (kw == name),
			_ => false,
		}
	}

	pub fn to_string(&self) -> String {
		match *self {
			Ampersand         => "&".to_string(),
			Apostrophe        => "'".to_string(),
			Arrow             => "=>".to_string(),
			Colon             => ":".to_string(),
			ColonEq           => ":=".to_string(),
			Comma             => ",".to_string(),
			Equal             => "=".to_string(),
			Gt                => ">".to_string(),
			GtEq              => ">=".to_string(),
			Lt                => "<".to_string(),
			LtEq              => "<=".to_string(),
			LtGt              => "<>".to_string(),
			Minus             => "-".to_string(),
			Period            => ".".to_string(),
			Pipe              => "|".to_string(),
			Plus              => "+".to_string(),
			Semicolon         => ";".to_string(),
			Slash             => "/".to_string(),
			SlashEq           => "/=".to_string(),
			Star              => "*".to_string(),
			StarStar          => "**".to_string(),

			OpenDelim(Paren)  => "(".to_string(),
			CloseDelim(Paren) => ")".to_string(),
			OpenDelim(Brack)  => "[".to_string(),
			CloseDelim(Brack) => "]".to_string(),
			OpenDelim(Brace)  => "{".to_string(),
			CloseDelim(Brace) => "}".to_string(),
			OpenDelim(Bgend)  => "begin".to_string(),
			CloseDelim(Bgend) => "end".to_string(),

			Ident(nm)         => nm.to_string(),

			_ => unimplemented!()
		}
	}
}


/// A delimiter token such as parentheses or brackets.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum DelimToken {
	/// A round paranthesis `(` or `)`
	Paren,
	/// A square bracket `[` or `]`
	Brack,
	/// A curly brace `{` or `}`
	Brace,
	/// A `begin` or `end`
	Bgend,
}


/// Abstract literals such as integers, reals, and strings.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Lit {
	Integer(Name),
	Real(Name, Option<Name>, Option<Name>),
	BasedInteger(u8, Name),
	BasedReal(u8, Name, Option<Name>, Option<Name>),
	Char(Name),
	Str(Name),
}


macro_rules! declare_keywords {(
	$( ($index: expr, $konst: ident, $string: expr) )*
) => {
	pub mod keywords {
		use name::{Name, NameTable};
		$(
			#[allow(non_upper_case_globals)]
			pub const $konst: Name = Name($index);
		)*

		pub fn prefill_name_table(nt: &mut NameTable) {
			$(
				nt.intern($string, false);
			)*
		}
	}
}}


declare_keywords! {
	// Invalid identifier
	(0,   Invalid,           "")

	// Keywords as per IEEE 1076-2000 13.3
	(1,   Abs,               "abs")
	(2,   Access,            "access")
	(3,   After,             "after")
	(4,   Alias,             "alias")
	(5,   All,               "all")
	(6,   And,               "and")
	(7,   Architecture,      "architecture")
	(8,   Array,             "array")
	(9,   Assert,            "assert")
	(10,  Assume,            "assume")
	(11,  AssumeGuarantee,   "assume_guarantee")
	(12,  Attribute,         "attribute")
	(13,  Begin,             "begin")
	(14,  Block,             "block")
	(15,  Body,              "body")
	(16,  Buffer,            "buffer")
	(17,  Bus,               "bus")
	(18,  Case,              "case")
	(19,  Component,         "component")
	(20,  Configuration,     "configuration")
	(21,  Constant,          "constant")
	(22,  Context,           "context")
	(23,  Cover,             "cover")
	(24,  Default,           "default")
	(25,  Disconnect,        "disconnect")
	(26,  Downto,            "downto")
	(27,  Else,              "else")
	(28,  Elsif,             "elsif")
	(29,  End,               "end")
	(30,  Entity,            "entity")
	(31,  Exit,              "exit")
	(32,  Fairness,          "fairness")
	(33,  File,              "file")
	(34,  For,               "for")
	(35,  Force,             "force")
	(36,  Function,          "function")
	(37,  Generate,          "generate")
	(38,  Generic,           "generic")
	(39,  Group,             "group")
	(40,  Guarded,           "guarded")
	(41,  If,                "if")
	(42,  Impure,            "impure")
	(43,  In,                "in")
	(44,  Inertial,          "inertial")
	(45,  Inout,             "inout")
	(46,  Is,                "is")
	(47,  Label,             "label")
	(48,  Library,           "library")
	(49,  Linkage,           "linkage")
	(50,  Literal,           "literal")
	(51,  Loop,              "loop")
	(52,  Map,               "map")
	(53,  Mod,               "mod")
	(54,  Nand,              "nand")
	(55,  New,               "new")
	(56,  Next,              "next")
	(57,  Nor,               "nor")
	(58,  Not,               "not")
	(59,  Null,              "null")
	(60,  Of,                "of")
	(61,  On,                "on")
	(62,  Open,              "open")
	(63,  Or,                "or")
	(64,  Others,            "others")
	(65,  Out,               "out")
	(66,  Package,           "package")
	(67,  Parameter,         "parameter")
	(68,  Port,              "port")
	(69,  Postponed,         "postponed")
	(70,  Procedure,         "procedure")
	(71,  Process,           "process")
	(72,  Property,          "property")
	(73,  Protected,         "protected")
	(74,  Pure,              "pure")
	(75,  Range,             "range")
	(76,  Record,            "record")
	(77,  Register,          "register")
	(78,  Reject,            "reject")
	(79,  Release,           "release")
	(80,  Rem,               "rem")
	(81,  Report,            "report")
	(82,  Restrict,          "restrict")
	(83,  RestrictGuarantee, "restrict_guarantee")
	(84,  Return,            "return")
	(85,  Rol,               "rol")
	(86,  Ror,               "ror")
	(87,  Select,            "select")
	(88,  Sequence,          "sequence")
	(89,  Severity,          "severity")
	(90,  Shared,            "shared")
	(91,  Signal,            "signal")
	(92,  Sla,               "sla")
	(93,  Sll,               "sll")
	(94,  Sra,               "sra")
	(95,  Srl,               "srl")
	(96,  Strong,            "strong")
	(97,  Subtype,           "subtype")
	(98,  Then,              "then")
	(99,  To,                "to")
	(100, Transport,         "transport")
	(101, Type,              "type")
	(102, Unaffected,        "unaffected")
	(103, Units,             "units")
	(104, Until,             "until")
	(105, Use,               "use")
	(106, Variable,          "variable")
	(107, Vmode,             "vmode")
	(108, Vprop,             "vprop")
	(109, Vunit,             "vunit")
	(110, Wait,              "wait")
	(111, When,              "when")
	(112, While,             "while")
	(113, With,              "with")
	(114, Xnor,              "xnor")
	(115, Xor,               "xor")
}

pub fn prefill_name_table(nt: &mut NameTable) {
	keywords::prefill_name_table(nt);
}
