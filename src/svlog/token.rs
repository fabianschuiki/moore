// Copyright (c) 2016 Fabian Schuiki

//! Defines all tokens that may result from performing lexical analysis on a
//! SystemVerilog source file. This module is inspired heavily by the tokens
//! used in the Rust compiler.

pub use self::DelimToken::*;
pub use self::Token::*;
pub use self::Lit::*;
use name::{Name, NameTable};


/// A primary token emitted by the lexer.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Token {
	// Symbols
	Amp,
	AmpAmp,
	AmpEq,
	At,
	Caret,
	CaretEq,
	CaretTilda,
	Colon,
	Comma,
	EqEq,
	Equal,
	Gt,
	GtEq,
	GtGt,
	Hash,
	Impl,
	Lt,
	LtEq,
	LtLt,
	Minus,
	MinusEq,
	MinusMinus,
	Mod,
	ModEq,
	Not,
	NotEq,
	Period,
	Pipe,
	PipeEq,
	PipePipe,
	Plus,
	PlusEq,
	PlusPlus,
	Quest,
	Semicolon,
	Slash,
	SlashEq,
	Star,
	StarEq,
	StarStar,
	Tilda,
	TildaAmp,
	TildaCaret,

	/// An opening delimiter
	OpenDelim(DelimToken),
	/// A closing delimiter
	CloseDelim(DelimToken),

	/// A literal
	Literal(Lit),
	/// A system task or function identifier, e.g. "$display"
	SysIdent(Name),
	/// A `define compiler directive
	Define(Name,Name),
	/// An `include compiler directive
	Include(Name),
	/// A compiler directive, e.g. "`timescale"
	CompDir(Name),
	/// An identifier
	Ident(Name),
	/// An escaped identifier
	EscIdent(Name),

	// The end of the input file
	Eof,
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
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Lit {
	Str(Name),
	Decimal(Name),
	BasedInteger(Option<Name>, char, Name),
	UnbasedUnsized(char),
}
