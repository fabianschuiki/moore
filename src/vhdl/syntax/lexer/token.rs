// Copyright (c) 2016-2020 Fabian Schuiki

pub use self::DelimToken::*;
pub use self::Token::*;
use moore_common::name::*;
use std;
use std::fmt::{Display, Formatter, Result};

/// A primary token as emitted by the lexer.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Token {
    /// A basic or extended identifier.
    Ident(Name),
    /// A literal.
    Lit(Literal),
    /// An opening delimiter.
    OpenDelim(DelimToken),
    /// A closing delimiter.
    CloseDelim(DelimToken),
    /// A keyword.
    Keyword(Kw),

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
    Pipe,
    Qmark,

    /// The end of the input file.
    Eof,
}

impl Token {
    pub fn as_str(self) -> &'static str {
        match self {
            Ident(_) => "identifier",
            Lit(l) => l.as_str(),
            OpenDelim(Paren) => "(",
            CloseDelim(Paren) => ")",
            OpenDelim(Brack) => "[",
            CloseDelim(Brack) => "]",
            Keyword(kw) => kw.as_str(),

            Period => ".",
            Comma => ",",
            Colon => ":",
            Semicolon => ";",
            Apostrophe => "'",
            Ampersand => "&",
            Arrow => "=>",
            Condition => "??",
            LtGt => "<>",
            VarAssign => ":=",
            Lshift => "<<",
            Rshift => ">>",
            Eq => "=",
            Neq => "/=",
            Lt => "<",
            Leq => "<=",
            Gt => ">",
            Geq => ">=",
            MatchEq => "?=",
            MatchNeq => "?/=",
            MatchLt => "?<",
            MatchLeq => "?<=",
            MatchGt => "?>",
            MatchGeq => "?>=",
            Add => "+",
            Sub => "-",
            Mul => "*",
            Div => "/",
            Pow => "**",
            Pipe => "|",
            Qmark => "?",

            Eof => "end of file",
        }
    }

    /// Checks if this token is a identifier.
    pub fn is_ident(self) -> bool {
        match self {
            Ident(_) => true,
            _ => false,
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match *self {
            Ident(n) => write!(f, "identifier `{}`", n),
            Lit(l) => write!(f, "{}", l.as_str()),
            Keyword(kw) => write!(f, "keyword `{}`", kw.as_str()),
            tkn => write!(f, "`{}`", tkn.as_str()),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, RustcEncodable, RustcDecodable)]
pub enum Literal {
    Abstract(
        /// Base
        Option<Name>,
        /// Integer part
        Name,
        /// Fractional part
        Option<Name>,
        /// Exponent
        Option<Exponent>,
    ),
    BitString(
        /// Size
        Option<Name>,
        /// Base
        BitStringBase,
        /// Value
        Name,
    ),
    Char(char),
    String(Name),
}

impl Literal {
    pub fn as_str(self) -> &'static str {
        match self {
            Literal::Abstract(..) => "abstract literal",
            Literal::BitString(..) => "bit string literal",
            Literal::Char(..) => "character literal",
            Literal::String(..) => "string literal",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum DelimToken {
    Paren,
    Brack,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, RustcEncodable, RustcDecodable)]
pub struct Exponent(
    /// Sign
    pub ExponentSign,
    /// Value
    pub Name,
);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, RustcEncodable, RustcDecodable)]
pub enum ExponentSign {
    Positive,
    Negative,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, RustcEncodable, RustcDecodable)]
pub enum BitStringBase {
    B,
    O,
    X,
    D,
    UB,
    UO,
    UX,
    SB,
    SO,
    SX,
}

/// Generates a `Kw` enum from a list of keywords.
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

    impl std::fmt::Display for Kw {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.as_str())
        }
    }

    pub fn find_keyword<S: AsRef<str>>(name: S) -> Option<Kw> {
        use std::collections::HashMap;
        use once_cell::sync::Lazy;
        static TBL: Lazy<HashMap<&'static str, Kw>> = Lazy::new(|| {
            let mut tbl = HashMap::new();
            $(
                assert!($string.chars().all(|c| !c.is_uppercase()));
                tbl.insert($string, Kw::$konst);
            )*
            tbl
        });
        TBL.get(name.as_ref().to_lowercase().as_str()).map(|kw| *kw)
    }
}}

declare_keywords! {
    // Keywords as per IEEE 1076-2008 section 15.10
    (Abs,                "abs")
    (Access,             "access")
    (After,              "after")
    (Alias,              "alias")
    (All,                "all")
    (And,                "and")
    (Architecture,       "architecture")
    (Array,              "array")
    (Assert,             "assert")
    (Assume,             "assume")
    (AssumeGuarantee,    "assume_guarantee")
    (Attribute,          "attribute")
    (Begin,              "begin")
    (Block,              "block")
    (Body,               "body")
    (Buffer,             "buffer")
    (Bus,                "bus")
    (Case,               "case")
    (Component,          "component")
    (Configuration,      "configuration")
    (Constant,           "constant")
    (Context,            "context")
    (Cover,              "cover")
    (Default,            "default")
    (Disconnect,         "disconnect")
    (Downto,             "downto")
    (Else,               "else")
    (Elsif,              "elsif")
    (End,                "end")
    (Entity,             "entity")
    (Exit,               "exit")
    (Fairness,           "fairness")
    (File,               "file")
    (For,                "for")
    (Force,              "force")
    (Function,           "function")
    (Generate,           "generate")
    (Generic,            "generic")
    (Group,              "group")
    (Guarded,            "guarded")
    (If,                 "if")
    (Impure,             "impure")
    (In,                 "in")
    (Inertial,           "inertial")
    (Inout,              "inout")
    (Is,                 "is")
    (Label,              "label")
    (Library,            "library")
    (Linkage,            "linkage")
    (Literal,            "literal")
    (Loop,               "loop")
    (Map,                "map")
    (Mod,                "mod")
    (Nand,               "nand")
    (New,                "new")
    (Next,               "next")
    (Nor,                "nor")
    (Not,                "not")
    (Null,               "null")
    (Of,                 "of")
    (On,                 "on")
    (Open,               "open")
    (Or,                 "or")
    (Others,             "others")
    (Out,                "out")
    (Package,            "package")
    (Parameter,          "parameter")
    (Port,               "port")
    (Postponed,          "postponed")
    (Procedure,          "procedure")
    (Process,            "process")
    (Property,           "property")
    (Protected,          "protected")
    (Pure,               "pure")
    (Range,              "range")
    (Record,             "record")
    (Register,           "register")
    (Reject,             "reject")
    (Release,            "release")
    (Rem,                "rem")
    (Report,             "report")
    (Restrict,           "restrict")
    (RestrictGuarantee,  "restrict_guarantee")
    (Return,             "return")
    (Rol,                "rol")
    (Ror,                "ror")
    (Select,             "select")
    (Sequence,           "sequence")
    (Severity,           "severity")
    (Shared,             "shared")
    (Signal,             "signal")
    (Sla,                "sla")
    (Sll,                "sll")
    (Sra,                "sra")
    (Srl,                "srl")
    (Strong,             "strong")
    (Subtype,            "subtype")
    (Then,               "then")
    (To,                 "to")
    (Transport,          "transport")
    (Type,               "type")
    (Unaffected,         "unaffected")
    (Units,              "units")
    (Until,              "until")
    (Use,                "use")
    (Variable,           "variable")
    (Vmode,              "vmode")
    (Vprop,              "vprop")
    (Vunit,              "vunit")
    (Wait,               "wait")
    (When,               "when")
    (While,              "while")
    (With,               "with")
    (Xnor,               "xnor")
    (Xor,                "xor")
}
