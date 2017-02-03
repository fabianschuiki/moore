// Copyright (c) 2016-2017 Fabian Schuiki

//! Defines all tokens that may result from performing lexical analysis on a
//! SystemVerilog source file. This module is inspired heavily by the tokens
//! used in the Rust compiler.

pub use self::DelimToken::*;
pub use self::Token::*;
pub use self::Lit::*;
use name::Name;
use std::fmt::{Display, Formatter, Result};


/// A primary token emitted by the lexer.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Token {
	// Symbols
	Comma,
	Period,
	Colon,
	Semicolon,
	At,
	Hashtag,
	DoubleHashtag,
	Namespace,
	Ternary,
	AddColon,
	SubColon,
	Apostrophe,
	Dollar,

	Operator(Op),

	/// An opening delimiter
	OpenDelim(DelimToken),
	/// A closing delimiter
	CloseDelim(DelimToken),

	/// A literal
	Literal(Lit),
	/// A system task or function identifier, e.g. "$display"
	SysIdent(Name),
	/// A compiler directive, e.g. "`timescale"
	CompDir(Name),
	/// An identifier
	Ident(Name),
	/// An escaped identifier
	EscIdent(Name),
	/// An unsigned number
	// UnsignedNumber(Name),
	/// A keyword
	Keyword(Kw),

	// The end of the input file
	Eof,
}

impl Token {
	pub fn as_str(self) -> &'static str {
		match self {
			// Symbols
			Comma         => ",",
			Period        => ".",
			Colon         => ":",
			Semicolon     => ";",
			At            => "@",
			Hashtag       => "#",
			DoubleHashtag => "##",
			Namespace     => "::",
			Ternary       => "?",
			AddColon      => "+:",
			SubColon      => "-:",
			Apostrophe    => "'",
			Dollar        => "$",

			Operator(op) => op.as_str(),

			// Opening and closing delimiters
			OpenDelim(Paren) => "(",
			OpenDelim(Brack) => "[",
			OpenDelim(Brace) => "{",
			OpenDelim(Bgend) => "begin",
			CloseDelim(Paren) => ")",
			CloseDelim(Brack) => "]",
			CloseDelim(Brace) => "}",
			CloseDelim(Bgend) => "end",

			Keyword(kw) => kw.as_str(),

			Literal(_)        => "literal",
			SysIdent(_)       => "system identifier",
			CompDir(_)        => "compiler directive",
			Ident(_)          => "identifier",
			EscIdent(_)       => "escaped identifier",

			Eof       => "end of file",
		}
	}
}

impl Display for Token {
	fn fmt(&self, f: &mut Formatter) -> Result {
		write!(f, "{}", self.as_str())
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


/// Abstract literals such as strings.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, RustcEncodable, RustcDecodable)]
pub enum Lit {
	Str(Name),
	Decimal(Name),
	/// An unsigned number.
	UnsignedInteger(Name),
	BasedInteger(Option<Name>, bool, char, Name),
	UnbasedUnsized(char),
	Real(Name),
	Time(Name),
}


/// Operator symbols.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, RustcEncodable, RustcDecodable)]
pub enum Op {
	// Assignment
	Assign,
	AssignAdd,
	AssignSub,
	AssignMul,
	AssignDiv,
	AssignMod,
	AssignBitAnd,
	AssignBitOr,
	AssignBitXor,
	AssignLogicShL,
	AssignLogicShR,
	AssignArithShL,
	AssignArithShR,

	// Arithmetic
	Add,
	Sub,
	Mul,
	Div,
	Mod,
	Pow,
	Inc,
	Dec,

	// Equality
	LogicEq,
	LogicNeq,
	CaseEq,
	CaseNeq,
	WildcardEq,
	WildcardNeq,

	// Relational
	Lt,
	Leq,
	Gt,
	Geq,

	// Logic
	LogicNot,
	LogicAnd,
	LogicOr,
	LogicImpl,
	LogicEquiv,

	// Bitwise
	BitNot,
	BitAnd,
	BitNand,
	BitOr,
	BitNor,
	BitXor,
	BitXnor,
	BitNxor,

	// Shift
	LogicShL,
	LogicShR,
	ArithShL,
	ArithShR,

	// Sequence
	SeqImplOl,
	SeqImplNol,
	SeqFollowOl,
	SeqFollowNol,
}

impl Op {
	pub fn as_str(self) -> &'static str {
		match self {
			// Assignment
			Op::Assign          => "=",
			Op::AssignAdd       => "+=",
			Op::AssignSub       => "-=",
			Op::AssignMul       => "*=",
			Op::AssignDiv       => "/=",
			Op::AssignMod       => "%=",
			Op::AssignBitAnd    => "&=",
			Op::AssignBitOr     => "|=",
			Op::AssignBitXor    => "^=",
			Op::AssignLogicShL  => "<<=",
			Op::AssignLogicShR  => ">>=",
			Op::AssignArithShL  => "<<<=",
			Op::AssignArithShR  => ">>>=",

			// Arithmetic
			Op::Add         => "+",
			Op::Sub         => "-",
			Op::Mul         => "*",
			Op::Div         => "/",
			Op::Mod         => "%",
			Op::Pow         => "**",
			Op::Inc         => "++",
			Op::Dec         => "--",

			// Equality
			Op::LogicEq     => "==",
			Op::LogicNeq    => "!=",
			Op::CaseEq      => "===",
			Op::CaseNeq     => "!==",
			Op::WildcardEq  => "==?",
			Op::WildcardNeq => "!=?",

			// Relational
			Op::Lt          => "<",
			Op::Leq         => "<=",
			Op::Gt          => ">",
			Op::Geq         => ">=",

			// Logic
			Op::LogicNot    => "!",
			Op::LogicAnd    => "&&",
			Op::LogicOr     => "||",
			Op::LogicImpl   => "->",
			Op::LogicEquiv  => "<->",

			// Bitwise
			Op::BitNot      => "~",
			Op::BitAnd      => "&",
			Op::BitNand     => "~&",
			Op::BitOr       => "|",
			Op::BitNor      => "~|",
			Op::BitXor      => "^",
			Op::BitXnor     => "^~",
			Op::BitNxor     => "~^",

			// Shift
			Op::LogicShL    => "<<",
			Op::LogicShR    => ">>",
			Op::ArithShL    => "<<<",
			Op::ArithShR    => ">>>",

			// Sequence
			Op::SeqImplOl    => "|->",
			Op::SeqImplNol   => "|=>",
			Op::SeqFollowOl  => "#-#",
			Op::SeqFollowNol => "#=#",
		}
	}

	pub fn get_precedence(self) -> Precedence {
		match self {
			// Assignment
			Op::Assign          |
			Op::AssignAdd       |
			Op::AssignSub       |
			Op::AssignMul       |
			Op::AssignDiv       |
			Op::AssignMod       |
			Op::AssignBitAnd    |
			Op::AssignBitOr     |
			Op::AssignBitXor    |
			Op::AssignLogicShL  |
			Op::AssignLogicShR  |
			Op::AssignArithShL  |
			Op::AssignArithShR  => Precedence::Assignment,

			// Arithmetic
			Op::Add         |
			Op::Sub         => Precedence::Add,
			Op::Mul         |
			Op::Div         |
			Op::Mod         => Precedence::Mul,
			Op::Pow         => Precedence::Pow,
			Op::Inc         |
			Op::Dec         => Precedence::Unary,

			// Equality
			Op::LogicEq     |
			Op::LogicNeq    |
			Op::CaseEq      |
			Op::CaseNeq     |
			Op::WildcardEq  |
			Op::WildcardNeq => Precedence::Equality,

			// Relational
			Op::Lt          |
			Op::Leq         |
			Op::Gt          |
			Op::Geq         => Precedence::Relational,

			// Logic
			Op::LogicNot    => Precedence::Unary,
			Op::LogicAnd    => Precedence::LogicAnd,
			Op::LogicOr     => Precedence::LogicOr,
			Op::LogicImpl   |
			Op::LogicEquiv  => Precedence::Implication,

			// Bitwise
			Op::BitNot      => Precedence::Unary,
			Op::BitAnd      => Precedence::BitAnd,
			Op::BitNand     => Precedence::Unary,
			Op::BitOr       => Precedence::BitOr,
			Op::BitNor      => Precedence::Unary,
			Op::BitXor      |
			Op::BitXnor     |
			Op::BitNxor     => Precedence::BitXor,

			// Shift
			Op::LogicShL    |
			Op::LogicShR    |
			Op::ArithShL    |
			Op::ArithShR    => Precedence::Shift,

			// Sequence
			Op::SeqImplOl    |
			Op::SeqImplNol   |
			Op::SeqFollowOl  |
			Op::SeqFollowNol => Precedence::Max,
		}
	}
}

impl Display for Op {
	fn fmt(&self, f: &mut Formatter) -> Result {
		write!(f, "{}", self.as_str())
	}
}


/// Expression precedence. Note that a few kinds of expression are
/// right-associative rather than the default left-associative.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
	Min,
	MinTypMax,
	Concatenation, // no associativity
	Assignment,    // no associativity
	Implication,   // right-associative
	Ternary,       // right-associative
	LogicOr,
	LogicAnd,
	BitOr,
	BitXor,
	BitAnd,
	Equality,
	Relational,
	Shift,
	Add,
	Mul,
	Pow,
	Unary,
	Postfix,
	Scope,
	Max,
}


macro_rules! declare_keywords {(
	$( ($konst: ident, $string: expr) )*
) => {
	#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug, Hash)]
	pub enum Kw {
		$($konst,)*
	}

	impl Kw {
		pub fn as_str(self) -> &'static str {
			match self {
				$(Kw::$konst => $string,)*
			}
		}
	}

	impl Display for Kw {
		fn fmt(&self, f: &mut Formatter) -> Result {
			write!(f, "{}", self.as_str())
		}
	}

	pub fn find_keyword<S: AsRef<str>>(name: S) -> Option<Kw> {
		use std::collections::HashMap;
		thread_local!(static TBL: HashMap<String,Kw> = {
			let mut tbl = HashMap::new();
			$(tbl.insert($string.into(), Kw::$konst);)*
			tbl
		});
		TBL.with(|tbl| tbl.get(name.as_ref()).map(|kw| *kw))
	}
}}


declare_keywords! {
	// Keywords as per IEEE 1800-2009 Table B.1
	(AcceptOn,             "accept_on")
	(Alias,                "alias")
	(Always,               "always")
	(AlwaysComb,           "always_comb")
	(AlwaysFf,             "always_ff")
	(AlwaysLatch,          "always_latch")
	(And,                  "and")
	(Assert,               "assert")
	(Assign,               "assign")
	(Assume,               "assume")
	(Automatic,            "automatic")
	(Before,               "before")
	(Begin,                "begin")
	(Bind,                 "bind")
	(Bins,                 "bins")
	(Binsof,               "binsof")
	(Bit,                  "bit")
	(Break,                "break")
	(Buf,                  "buf")
	(Bufif0,               "bufif0")
	(Bufif1,               "bufif1")
	(Byte,                 "byte")
	(Case,                 "case")
	(Casex,                "casex")
	(Casez,                "casez")
	(Cell,                 "cell")
	(Chandle,              "chandle")
	(Checker,              "checker")
	(Class,                "class")
	(Clocking,             "clocking")
	(Cmos,                 "cmos")
	(Config,               "config")
	(Const,                "const")
	(Constraint,           "constraint")
	(Context,              "context")
	(Continue,             "continue")
	(Cover,                "cover")
	(Covergroup,           "covergroup")
	(Coverpoint,           "coverpoint")
	(Cross,                "cross")
	(Deassign,             "deassign")
	(Default,              "default")
	(Defparam,             "defparam")
	(Design,               "design")
	(Disable,              "disable")
	(Dist,                 "dist")
	(Do,                   "do")
	(Edge,                 "edge")
	(Else,                 "else")
	(End,                  "end")
	(Endcase,              "endcase")
	(Endchecker,           "endchecker")
	(Endclass,             "endclass")
	(Endclocking,          "endclocking")
	(Endconfig,            "endconfig")
	(Endfunction,          "endfunction")
	(Endgenerate,          "endgenerate")
	(Endgroup,             "endgroup")
	(Endinterface,         "endinterface")
	(Endmodule,            "endmodule")
	(Endpackage,           "endpackage")
	(Endprimitive,         "endprimitive")
	(Endprogram,           "endprogram")
	(Endproperty,          "endproperty")
	(Endsequence,          "endsequence")
	(Endspecify,           "endspecify")
	(Endtable,             "endtable")
	(Endtask,              "endtask")
	(Enum,                 "enum")
	(Event,                "event")
	(Eventually,           "eventually")
	(Expect,               "expect")
	(Export,               "export")
	(Extends,              "extends")
	(Extern,               "extern")
	(Final,                "final")
	(FirstMatch,           "first_match")
	(For,                  "for")
	(Force,                "force")
	(Foreach,              "foreach")
	(Forever,              "forever")
	(Fork,                 "fork")
	(Forkjoin,             "forkjoin")
	(Function,             "function")
	(Generate,             "generate")
	(Genvar,               "genvar")
	(Global,               "global")
	(Highz0,               "highz0")
	(Highz1,               "highz1")
	(If,                   "if")
	(Iff,                  "iff")
	(Ifnone,               "ifnone")
	(IgnoreBins,           "ignore_bins")
	(IllegalBins,          "illegal_bins")
	(Implies,              "implies")
	(Import,               "import")
	(Incdir,               "incdir")
	(Include,              "include")
	(Initial,              "initial")
	(Inout,                "inout")
	(Input,                "input")
	(Inside,               "inside")
	(Instance,             "instance")
	(Int,                  "int")
	(Integer,              "integer")
	(Interface,            "interface")
	(Intersect,            "intersect")
	(Join,                 "join")
	(JoinAny,              "join_any")
	(JoinNone,             "join_none")
	(Large,                "large")
	(Let,                  "let")
	(Liblist,              "liblist")
	(Library,              "library")
	(Local,                "local")
	(Localparam,           "localparam")
	(Logic,                "logic")
	(Longint,              "longint")
	(Macromodule,          "macromodule")
	(Matches,              "matches")
	(Medium,               "medium")
	(Modport,              "modport")
	(Module,               "module")
	(Nand,                 "nand")
	(Negedge,              "negedge")
	(New,                  "new")
	(Nexttime,             "nexttime")
	(Nmos,                 "nmos")
	(Nor,                  "nor")
	(Noshowcancelled,      "noshowcancelled")
	(Not,                  "not")
	(Notif0,               "notif0")
	(Notif1,               "notif1")
	(Null,                 "null")
	(Or,                   "or")
	(Output,               "output")
	(Package,              "package")
	(Packed,               "packed")
	(Parameter,            "parameter")
	(Pmos,                 "pmos")
	(Posedge,              "posedge")
	(Primitive,            "primitive")
	(Priority,             "priority")
	(Program,              "program")
	(Property,             "property")
	(Protected,            "protected")
	(Pull0,                "pull0")
	(Pull1,                "pull1")
	(Pulldown,             "pulldown")
	(Pullup,               "pullup")
	(PulsestyleOndetect,   "pulsestyle_ondetect")
	(PulsestyleOnevent,    "pulsestyle_onevent")
	(Pure,                 "pure")
	(Rand,                 "rand")
	(Randc,                "randc")
	(Randcase,             "randcase")
	(Randsequence,         "randsequence")
	(Rcmos,                "rcmos")
	(Real,                 "real")
	(Realtime,             "realtime")
	(Ref,                  "ref")
	(Reg,                  "reg")
	(RejectOn,             "reject_on")
	(Release,              "release")
	(Repeat,               "repeat")
	(Restrict,             "restrict")
	(Return,               "return")
	(Rnmos,                "rnmos")
	(Rpmos,                "rpmos")
	(Rtran,                "rtran")
	(Rtranif0,             "rtranif0")
	(Rtranif1,             "rtranif1")
	(SAlways,              "s_always")
	(SEventually,          "s_eventually")
	(SNexttime,            "s_nexttime")
	(SUntil,               "s_until")
	(SUntilWith,           "s_until_with")
	(Scalared,             "scalared")
	(Sequence,             "sequence")
	(Shortint,             "shortint")
	(Shortreal,            "shortreal")
	(Showcancelled,        "showcancelled")
	(Signed,               "signed")
	(Small,                "small")
	(Solve,                "solve")
	(Specify,              "specify")
	(Specparam,            "specparam")
	(Static,               "static")
	(String,               "string")
	(Strong,               "strong")
	(Strong0,              "strong0")
	(Strong1,              "strong1")
	(Struct,               "struct")
	(Super,                "super")
	(Supply0,              "supply0")
	(Supply1,              "supply1")
	(SyncAcceptOn,         "sync_accept_on")
	(SyncRejectOn,         "sync_reject_on")
	(Table,                "table")
	(Tagged,               "tagged")
	(Task,                 "task")
	(This,                 "this")
	(Throughout,           "throughout")
	(Time,                 "time")
	(Timeprecision,        "timeprecision")
	(Timeunit,             "timeunit")
	(Tran,                 "tran")
	(Tranif0,              "tranif0")
	(Tranif1,              "tranif1")
	(Tri,                  "tri")
	(Tri0,                 "tri0")
	(Tri1,                 "tri1")
	(Triand,               "triand")
	(Trior,                "trior")
	(Trireg,               "trireg")
	(Type,                 "type")
	(Typedef,              "typedef")
	(Union,                "union")
	(Unique,               "unique")
	(Unique0,              "unique0")
	(Unsigned,             "unsigned")
	(Until,                "until")
	(UntilWith,            "until_with")
	(Untyped,              "untyped")
	(Use,                  "use")
	(Uwire,                "uwire")
	(Var,                  "var")
	(Vectored,             "vectored")
	(Virtual,              "virtual")
	(Void,                 "void")
	(Wait,                 "wait")
	(WaitOrder,            "wait_order")
	(Wand,                 "wand")
	(Weak,                 "weak")
	(Weak0,                "weak0")
	(Weak1,                "weak1")
	(While,                "while")
	(Wildcard,             "wildcard")
	(Wire,                 "wire")
	(With,                 "with")
	(Within,               "within")
	(Wor,                  "wor")
	(Xnor,                 "xnor")
	(Xor,                  "xor")
}
