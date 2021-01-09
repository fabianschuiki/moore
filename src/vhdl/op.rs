// Copyright (c) 2016-2021 Fabian Schuiki

//! Operators

#![deny(missing_docs)]

use std::collections::HashMap;
use std::fmt;

use crate::common::errors::*;
use crate::common::name::*;
use crate::common::score::Result;
use crate::common::source::Spanned;

use crate::score::ResolvableName;
use crate::syntax::ast;
pub use crate::syntax::ast::LogicalOp;
pub use crate::syntax::ast::RelationalOp;
pub use crate::syntax::ast::ShiftOp;

/// An operator.
///
/// See IEEE 1076-2008 section 9.2.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operator {
    /// A logical operator.
    Logical(LogicalOp),
    /// A relational operator.
    Rel(RelationalOp),
    /// A matching relational operator (i.e. with `?` prefix).
    Match(RelationalOp),
    /// A shift operator.
    Shift(ShiftOp),
    /// Addition or positive sign `+`.
    Add,
    /// Subtraction or negative sign `-`.
    Sub,
    /// Concatenation `&`.
    Concat,
    /// Multiplication `*`.
    Mul,
    /// Division `/`.
    Div,
    /// Modulus `mod`.
    Mod,
    /// Remainder `rem`.
    Rem,
    /// Power `**`.
    Pow,
    /// Absolute value `abs`.
    Abs,
    /// Boolean negation `not.
    Not,
    /// Condition operator `??`.
    Cond,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Operator::Logical(op) => write!(f, "{}", op),
            Operator::Rel(op) => write!(f, "{}", op),
            Operator::Match(op) => write!(f, "?{}", op),
            Operator::Shift(op) => write!(f, "{}", op),
            Operator::Add => write!(f, "+"),
            Operator::Sub => write!(f, "-"),
            Operator::Concat => write!(f, "&"),
            Operator::Mul => write!(f, "*"),
            Operator::Div => write!(f, "/"),
            Operator::Mod => write!(f, "mod"),
            Operator::Rem => write!(f, "rem"),
            Operator::Pow => write!(f, "**"),
            Operator::Abs => write!(f, "abs"),
            Operator::Not => write!(f, "not"),
            Operator::Cond => write!(f, "??"),
        }
    }
}

impl Operator {
    /// Map a name to an operator.
    ///
    /// Returns `None` if no such operator exists.
    pub fn from_name(name: Name) -> Option<Operator> {
        TBL.get(&name).map(|&o| o)
    }
}

// A static table that maps operator symbols to the actual operator.
lazy_static! {
    static ref TBL: HashMap<Name, Operator> = {
        let mut tbl = HashMap::new();
        let nt = get_name_table();
        tbl.insert(nt.intern("and", false), Operator::Logical(LogicalOp::And));
        tbl.insert(nt.intern("or", false), Operator::Logical(LogicalOp::Or));
        tbl.insert(nt.intern("nand", false), Operator::Logical(LogicalOp::Nand));
        tbl.insert(nt.intern("nor", false), Operator::Logical(LogicalOp::Nor));
        tbl.insert(nt.intern("xor", false), Operator::Logical(LogicalOp::Xor));
        tbl.insert(nt.intern("xnor", false), Operator::Logical(LogicalOp::Xnor));
        tbl.insert(nt.intern("=", false), Operator::Rel(RelationalOp::Eq));
        tbl.insert(nt.intern("/=", false), Operator::Rel(RelationalOp::Neq));
        tbl.insert(nt.intern("<", false), Operator::Rel(RelationalOp::Lt));
        tbl.insert(nt.intern("<=", false), Operator::Rel(RelationalOp::Leq));
        tbl.insert(nt.intern(">", false), Operator::Rel(RelationalOp::Gt));
        tbl.insert(nt.intern(">=", false), Operator::Rel(RelationalOp::Geq));
        tbl.insert(nt.intern("?=", false), Operator::Match(RelationalOp::Eq));
        tbl.insert(nt.intern("?/=", false), Operator::Match(RelationalOp::Neq));
        tbl.insert(nt.intern("?<", false), Operator::Match(RelationalOp::Lt));
        tbl.insert(nt.intern("?<=", false), Operator::Match(RelationalOp::Leq));
        tbl.insert(nt.intern("?>", false), Operator::Match(RelationalOp::Gt));
        tbl.insert(nt.intern("?>=", false), Operator::Match(RelationalOp::Geq));
        tbl.insert(nt.intern("sll", false), Operator::Shift(ShiftOp::Sll));
        tbl.insert(nt.intern("srl", false), Operator::Shift(ShiftOp::Srl));
        tbl.insert(nt.intern("sla", false), Operator::Shift(ShiftOp::Sla));
        tbl.insert(nt.intern("sra", false), Operator::Shift(ShiftOp::Sra));
        tbl.insert(nt.intern("rol", false), Operator::Shift(ShiftOp::Rol));
        tbl.insert(nt.intern("ror", false), Operator::Shift(ShiftOp::Ror));
        tbl.insert(nt.intern("+", false), Operator::Add);
        tbl.insert(nt.intern("-", false), Operator::Sub);
        tbl.insert(nt.intern("&", false), Operator::Concat);
        tbl.insert(nt.intern("*", false), Operator::Mul);
        tbl.insert(nt.intern("/", false), Operator::Div);
        tbl.insert(nt.intern("mod", false), Operator::Mod);
        tbl.insert(nt.intern("rem", false), Operator::Rem);
        tbl.insert(nt.intern("**", false), Operator::Pow);
        tbl.insert(nt.intern("abs", false), Operator::Abs);
        tbl.insert(nt.intern("not", false), Operator::Not);
        tbl
    };
}

/// A unary operator.
///
/// See IEEE 1076-2008 section 9.2.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum UnaryOp {
    /// The `not` operator.
    Not,
    /// The `abs` operator.
    Abs,
    /// The `+` sign operator.
    Pos,
    /// The `-` sign operator.
    Neg,
    /// A logical operator.
    Logical(LogicalOp),
    /// The `??` operator.
    Cond,
}

impl UnaryOp {
    /// Map an AST unary operator to a HIR unary operator.
    ///
    /// Emits an error if the operator is not a valid unary operator.
    pub fn from<C: DiagEmitter>(ast: Spanned<ast::UnaryOp>, ctx: C) -> Result<Spanned<UnaryOp>> {
        let op = match ast.value {
            ast::UnaryOp::Not => UnaryOp::Not,
            ast::UnaryOp::Abs => UnaryOp::Abs,
            ast::UnaryOp::Sign(ast::Sign::Pos) => UnaryOp::Pos,
            ast::UnaryOp::Sign(ast::Sign::Neg) => UnaryOp::Neg,
            ast::UnaryOp::Logical(op) => UnaryOp::Logical(op),
            ast::UnaryOp::Condition => UnaryOp::Cond,
            _ => {
                ctx.emit(DiagBuilder2::error("invalid unary operator").span(ast.span));
                return Err(());
            }
        };
        Ok(Spanned::new(op, ast.span))
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            UnaryOp::Not => write!(f, "not"),
            UnaryOp::Abs => write!(f, "abs"),
            UnaryOp::Pos => write!(f, "+"),
            UnaryOp::Neg => write!(f, "-"),
            UnaryOp::Logical(op) => write!(f, "{}", op),
            UnaryOp::Cond => write!(f, "??"),
        }
    }
}

impl From<UnaryOp> for Operator {
    fn from(op: UnaryOp) -> Operator {
        match op {
            UnaryOp::Not => Operator::Not,
            UnaryOp::Abs => Operator::Abs,
            UnaryOp::Pos => Operator::Add,
            UnaryOp::Neg => Operator::Sub,
            UnaryOp::Logical(op) => Operator::Logical(op),
            UnaryOp::Cond => Operator::Cond,
        }
    }
}

impl From<UnaryOp> for ResolvableName {
    fn from(op: UnaryOp) -> ResolvableName {
        ResolvableName::Operator(op.into())
    }
}

/// A binary operator.
///
/// See IEEE 1076-2008 section 9.2.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BinaryOp {
    /// A logical operator.
    Logical(LogicalOp),
    /// A relational operator.
    Rel(RelationalOp),
    /// A matching relational operator. These are the relational operators
    /// prefixed with a `?`.
    Match(RelationalOp),
    /// A shift operator.
    Shift(ShiftOp),
    /// The `+` operator.
    Add,
    /// The `-` operator.
    Sub,
    /// The `&` operator.
    Concat,
    /// The `*` operator.
    Mul,
    /// The `/` operator.
    Div,
    /// The `mod` operator.
    Mod,
    /// The `rem` operator.
    Rem,
    /// The `**` operator.
    Pow,
}

impl BinaryOp {
    /// Map an AST binary operator to a HIR binary operator.
    ///
    /// Emits an error if the operator is not a valid binary operator.
    pub fn from<C: DiagEmitter>(ast: Spanned<ast::BinaryOp>, ctx: C) -> Result<Spanned<BinaryOp>> {
        let op = match ast.value {
            ast::BinaryOp::Logical(op) => BinaryOp::Logical(op),
            ast::BinaryOp::Rel(op) => BinaryOp::Rel(op),
            ast::BinaryOp::Match(op) => BinaryOp::Match(op),
            ast::BinaryOp::Shift(op) => BinaryOp::Shift(op),
            ast::BinaryOp::Add => BinaryOp::Add,
            ast::BinaryOp::Sub => BinaryOp::Sub,
            ast::BinaryOp::Concat => BinaryOp::Concat,
            ast::BinaryOp::Mul => BinaryOp::Mul,
            ast::BinaryOp::Div => BinaryOp::Div,
            ast::BinaryOp::Mod => BinaryOp::Mod,
            ast::BinaryOp::Rem => BinaryOp::Rem,
            ast::BinaryOp::Pow => BinaryOp::Pow,
            _ => {
                ctx.emit(DiagBuilder2::error("invalid binary operator").span(ast.span));
                return Err(());
            }
        };
        Ok(Spanned::new(op, ast.span))
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BinaryOp::Logical(op) => write!(f, "{}", op),
            BinaryOp::Rel(op) => write!(f, "{}", op),
            BinaryOp::Match(op) => write!(f, "?{}", op),
            BinaryOp::Shift(op) => write!(f, "{}", op),
            BinaryOp::Add => write!(f, "+"),
            BinaryOp::Sub => write!(f, "-"),
            BinaryOp::Concat => write!(f, "&"),
            BinaryOp::Mul => write!(f, "*"),
            BinaryOp::Div => write!(f, "/"),
            BinaryOp::Mod => write!(f, "mod"),
            BinaryOp::Rem => write!(f, "rem"),
            BinaryOp::Pow => write!(f, "**"),
        }
    }
}

impl From<BinaryOp> for Operator {
    fn from(op: BinaryOp) -> Operator {
        match op {
            BinaryOp::Logical(op) => Operator::Logical(op),
            BinaryOp::Rel(op) => Operator::Rel(op),
            BinaryOp::Match(op) => Operator::Match(op),
            BinaryOp::Shift(op) => Operator::Shift(op),
            BinaryOp::Add => Operator::Add,
            BinaryOp::Sub => Operator::Sub,
            BinaryOp::Concat => Operator::Concat,
            BinaryOp::Mul => Operator::Mul,
            BinaryOp::Div => Operator::Div,
            BinaryOp::Mod => Operator::Mod,
            BinaryOp::Rem => Operator::Rem,
            BinaryOp::Pow => Operator::Pow,
        }
    }
}

impl From<BinaryOp> for ResolvableName {
    fn from(op: BinaryOp) -> ResolvableName {
        ResolvableName::Operator(op.into())
    }
}
