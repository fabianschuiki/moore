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
	Colon,
	Comma,
	Equal,
	Gt,
	Hash,
	Lt,
	Minus,
	Period,
	Plus,
	Semicolon,
	Slash,
	Star,

	/// An opening delimiter
	OpenDelim(DelimToken),
	/// A closing delimiter
	CloseDelim(DelimToken),

	/// A literal
	Literal(Lit),
	/// A system task or function identifier, e.g. "$display"
	SysIdent(Name),
	/// A compiler directive, e.g. "`include"
	CompDir(Name),
	/// An identifier
	Ident(Name),

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
}
