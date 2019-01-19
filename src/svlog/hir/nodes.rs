// Copyright (c) 2017 Fabian Schuiki

//! This module contains the nodes of the tree structure that is the HIR.

use crate::crate_prelude::*;
use num::{BigInt, BigRational};

/// A reference to an HIR node.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum HirNode<'hir> {
    Module(&'hir Module<'hir>),
    Port(&'hir Port),
    Type(&'hir Type),
    Expr(&'hir Expr),
    InstTarget(&'hir InstTarget),
    Inst(&'hir Inst<'hir>),
    TypeParam(&'hir TypeParam),
    ValueParam(&'hir ValueParam),
    VarDecl(&'hir VarDecl),
    Proc(&'hir Proc),
    Stmt(&'hir Stmt),
    EventExpr(&'hir EventExpr),
    Gen(&'hir Gen),
    // Interface(&'hir Interface),
    // Package(&'hir Package),
    // PortSlice(&'hir PortSlice),
}

impl<'hir> HasSpan for HirNode<'hir> {
    fn span(&self) -> Span {
        match *self {
            HirNode::Module(x) => x.span(),
            HirNode::Port(x) => x.span(),
            HirNode::Type(x) => x.span(),
            HirNode::Expr(x) => x.span(),
            HirNode::InstTarget(x) => x.span(),
            HirNode::Inst(x) => x.span(),
            HirNode::TypeParam(x) => x.span(),
            HirNode::ValueParam(x) => x.span(),
            HirNode::VarDecl(x) => x.span(),
            HirNode::Proc(x) => x.span(),
            HirNode::Stmt(x) => x.span(),
            HirNode::EventExpr(x) => x.span(),
            HirNode::Gen(x) => x.span(),
        }
    }

    fn human_span(&self) -> Span {
        match *self {
            HirNode::Module(x) => x.human_span(),
            HirNode::Port(x) => x.human_span(),
            HirNode::Type(x) => x.human_span(),
            HirNode::Expr(x) => x.human_span(),
            HirNode::InstTarget(x) => x.human_span(),
            HirNode::Inst(x) => x.human_span(),
            HirNode::TypeParam(x) => x.human_span(),
            HirNode::ValueParam(x) => x.human_span(),
            HirNode::VarDecl(x) => x.human_span(),
            HirNode::Proc(x) => x.human_span(),
            HirNode::Stmt(x) => x.human_span(),
            HirNode::EventExpr(x) => x.human_span(),
            HirNode::Gen(x) => x.human_span(),
        }
    }
}

impl<'hir> HasDesc for HirNode<'hir> {
    fn desc(&self) -> &'static str {
        match *self {
            HirNode::Module(x) => x.desc(),
            HirNode::Port(x) => x.desc(),
            HirNode::Type(x) => x.desc(),
            HirNode::Expr(x) => x.desc(),
            HirNode::InstTarget(x) => x.desc(),
            HirNode::Inst(x) => x.desc(),
            HirNode::TypeParam(x) => x.desc(),
            HirNode::ValueParam(x) => x.desc(),
            HirNode::VarDecl(x) => x.desc(),
            HirNode::Proc(x) => x.desc(),
            HirNode::Stmt(x) => x.desc(),
            HirNode::EventExpr(x) => x.desc(),
            HirNode::Gen(x) => x.desc(),
        }
    }

    fn desc_full(&self) -> String {
        match *self {
            HirNode::Module(x) => x.desc_full(),
            HirNode::Port(x) => x.desc_full(),
            HirNode::Type(x) => x.desc_full(),
            HirNode::Expr(x) => x.desc_full(),
            HirNode::InstTarget(x) => x.desc_full(),
            HirNode::Inst(x) => x.desc_full(),
            HirNode::TypeParam(x) => x.desc_full(),
            HirNode::ValueParam(x) => x.desc_full(),
            HirNode::VarDecl(x) => x.desc_full(),
            HirNode::Proc(x) => x.desc_full(),
            HirNode::Stmt(x) => x.desc_full(),
            HirNode::EventExpr(x) => x.desc_full(),
            HirNode::Gen(x) => x.desc_full(),
        }
    }
}

/// A module.
#[derive(Debug, PartialEq, Eq)]
pub struct Module<'hir> {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    // pub lifetime: ast::Lifetime,
    pub ports: &'hir [NodeId],
    pub params: &'hir [NodeId],
    // pub body: HierarchyBody,
    /// The module/interface instances in the module.
    pub insts: &'hir [NodeId],
    /// The variable and net declarations in the module.
    pub decls: &'hir [NodeId],
    /// The procedures in the module.
    pub procs: &'hir [NodeId],
    /// The generate blocks in the module.
    pub gens: &'hir [NodeId],
}

impl HasSpan for Module<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for Module<'_> {
    fn desc(&self) -> &'static str {
        "module"
    }

    fn desc_full(&self) -> String {
        format!("module `{}`", self.name.value)
    }
}

/// An instantiation target.
///
/// In an instantiation `foo #(...) a(), b(), c();` this struct represents the
/// `foo #(...)` part. Multiple instantiations (`a()`, `b()`, `c()`) may share
/// the same target.
#[derive(Debug, PartialEq, Eq)]
pub struct InstTarget {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    pub pos_params: Vec<PosParam>,
    pub named_params: Vec<NamedParam>,
}

impl HasSpan for InstTarget {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for InstTarget {
    fn desc(&self) -> &'static str {
        "instantiation"
    }

    fn desc_full(&self) -> String {
        format!("`{}` instantiation", self.name.value)
    }
}

/// A positional parameter.
pub type PosParam = (Span, NodeId);

/// A named parameter.
pub type NamedParam = (Span, Spanned<Name>, NodeId);

/// An instantiation.
///
/// In an instantiation `foo #(...) a(), b(), c();`, this struct represents the
/// `a()` part.
#[derive(Debug, PartialEq, Eq)]
pub struct Inst<'hir> {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    /// The target of the instantiation.
    pub target: NodeId,
    pub dummy: std::marker::PhantomData<&'hir ()>,
}

impl HasSpan for Inst<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for Inst<'_> {
    fn desc(&self) -> &'static str {
        "instance"
    }

    fn desc_full(&self) -> String {
        format!("instance `{}`", self.name.value)
    }
}

/// A type parameter.
#[derive(Debug, PartialEq, Eq)]
pub struct TypeParam {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    pub local: bool,
    pub default: Option<NodeId>,
}

impl HasSpan for TypeParam {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for TypeParam {
    fn desc(&self) -> &'static str {
        "type parameter"
    }

    fn desc_full(&self) -> String {
        format!("type parameter `{}`", self.name.value)
    }
}

/// A value parameter.
#[derive(Debug, PartialEq, Eq)]
pub struct ValueParam {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    pub local: bool,
    pub ty: NodeId,
    pub default: Option<NodeId>,
}

impl HasSpan for ValueParam {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for ValueParam {
    fn desc(&self) -> &'static str {
        "parameter"
    }

    fn desc_full(&self) -> String {
        format!("parameter `{}`", self.name.value)
    }
}

// /// An interface.
// pub struct Interface {
//     pub id: NodeId,
//     pub name: Name,
//     pub span: Span,
//     pub lifetime: ast::Lifetime,
//     pub ports: Vec<Port>,
//     pub params: Vec<ast::ParamDecl>,
//     pub body: HierarchyBody,
// }

// /// A package.
// pub struct Package {
//     pub name: Name,
//     pub span: Span,
//     pub lifetime: ast::Lifetime,
//     pub body: HierarchyBody,
// }

// /// A hierarchy body represents the contents of a module, interface, or package.
// /// Generate regions and nested modules introduce additional bodies. The point
// /// of hierarchy bodies is to take a level of the design hierarchy and group all
// /// declarations by type, rather than having them in a single array in
// /// declaration order.
// pub struct HierarchyBody {
//     pub procs: Vec<ast::Procedure>,
//     pub nets: Vec<ast::NetDecl>,
//     pub vars: Vec<ast::VarDecl>,
//     pub assigns: Vec<ast::ContAssign>,
//     pub params: Vec<ast::ParamDecl>,
//     pub insts: Vec<ast::Inst>,
//     pub genreg: Vec<HierarchyBody>,
//     pub genvars: Vec<ast::GenvarDecl>,
//     pub genfors: Vec<GenerateFor>,
//     pub genifs: Vec<GenerateIf>,
//     pub gencases: Vec<ast::GenerateCase>,
//     pub classes: Vec<ast::ClassDecl>, // TODO: Make this an HIR node, since it contains hierarchy items
//     pub subroutines: Vec<ast::SubroutineDecl>, // TODO: Make this an HIR node
//     pub asserts: Vec<ast::Assertion>,
//     pub typedefs: Vec<ast::Typedef>,
// }

/// A module or interface port.
#[derive(Debug, PartialEq, Eq)]
pub struct Port {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    pub dir: ast::PortDir,
    pub ty: NodeId,
    pub default: Option<NodeId>,
}

impl HasSpan for Port {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for Port {
    fn desc(&self) -> &'static str {
        "port"
    }

    fn desc_full(&self) -> String {
        format!("port `{}`", self.name.value)
    }
}

// /// A port slice refers to a port declaration within the module. It consists of
// /// the name of the declaration and a list of optional member and index accesses
// /// that select individual parts of the declaration.
// #[derive(Debug)]
// pub struct PortSlice {
//     pub id: NodeId,
//     pub name: Name,
//     pub span: Span,
//     pub selects: Vec<PortSelect>,
//     pub dir: ast::PortDir,
//     pub kind: ast::PortKind,
//     pub ty: Option<ast::Type>,
//     pub dims: Vec<ast::TypeDim>,
// }

// #[derive(Debug)]
// pub enum PortSelect {
//     Member(Span, Name),
//     Index(Span, Expr),
// }

// pub struct PortDecl {
//     pub dir: ast::PortDir,
// }

// pub enum PortDir {

// }

// pub struct GenerateBlock {
//     pub span: Span,
//     pub label: Option<Name>,
//     pub body: HierarchyBody,
// }

// pub struct GenerateFor {
//     pub span: Span,
//     pub init: ast::Stmt,
//     pub cond: ast::Expr,
//     pub step: ast::Expr,
//     pub block: GenerateBlock,
// }

// pub struct GenerateIf {
//     pub span: Span,
//     pub cond: ast::Expr,
//     pub main_block: GenerateBlock,
//     pub else_block: Option<GenerateBlock>,
// }

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    pub id: NodeId,
    pub span: Span,
    pub kind: TypeKind,
}

impl HasSpan for Type {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Type {
    fn desc(&self) -> &'static str {
        #[allow(unreachable_patterns)]
        match self.kind {
            TypeKind::Builtin(BuiltinType::Void) => "void type",
            TypeKind::Builtin(BuiltinType::Bit) => "bit type",
            TypeKind::Builtin(BuiltinType::Logic) => "logic type",
            TypeKind::Builtin(BuiltinType::Byte) => "byte type",
            TypeKind::Builtin(BuiltinType::ShortInt) => "short int type",
            TypeKind::Builtin(BuiltinType::Int) => "int type",
            TypeKind::Builtin(BuiltinType::LongInt) => "long int type",
            _ => "type",
        }
    }

    fn desc_full(&self) -> String {
        match self.kind {
            TypeKind::Named(n) => format!("type `{}`", n.value),
            _ => self.desc().into(),
        }
    }
}

/// The different forms a type can take.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    /// A builtin type.
    Builtin(BuiltinType),
    /// A named type.
    Named(Spanned<Name>),
}

/// A builtin type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinType {
    Void,
    Bit,
    Logic,
    Byte,
    ShortInt,
    Int,
    LongInt,
}

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub id: NodeId,
    pub span: Span,
    pub kind: ExprKind,
}

impl HasSpan for Expr {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Expr {
    fn desc(&self) -> &'static str {
        #[allow(unreachable_patterns)]
        match self.kind {
            ExprKind::IntConst(_) => "integer constant",
            ExprKind::TimeConst(_) => "time constant",
            ExprKind::Ident(_) => "identifier",
            _ => "expression",
        }
    }

    fn desc_full(&self) -> String {
        #[allow(unreachable_patterns)]
        match self.kind {
            ExprKind::IntConst(ref k) => format!("{} `{}`", self.desc(), k),
            ExprKind::TimeConst(ref k) => format!("{} `{}`", self.desc(), k),
            ExprKind::Ident(n) => format!("{} `{}`", self.desc(), n.value),
            _ => format!("{} `{}`", self.desc(), self.span().extract()),
        }
    }
}

/// The different forms an expression can take.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    /// An integer constant literal.
    IntConst(BigInt),
    /// A time constant literal.
    TimeConst(BigRational),
    /// An identifier.
    Ident(Spanned<Name>),
    /// A unary operator.
    Unary(UnaryOp, NodeId),
    /// A binary operator.
    Binary(BinaryOp, NodeId, NodeId),
}

/// The different unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// The bitwise not operator `~x`.
    BitNot,
    /// The not operator `!x`.
    LogicNot,
    /// The prefix increment operator `++x`.
    PreInc,
    /// The prefix decrement operator `--x`.
    PreDec,
    /// The postfix increment operator `x++`.
    PostInc,
    /// The postfix decrement operator `x--`.
    PostDec,
}

impl HasDesc for UnaryOp {
    fn desc(&self) -> &'static str {
        match *self {
            UnaryOp::BitNot => "`~` operator",
            UnaryOp::LogicNot => "`!` operator",
            UnaryOp::PreInc => "`++` prefix operator",
            UnaryOp::PreDec => "`--` prefix operator",
            UnaryOp::PostInc => "`++` postfix operator",
            UnaryOp::PostDec => "`--` postfix operator",
        }
    }
}

/// The different binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    /// The addition operator `x + y`.
    Add,
    /// The subtraction operator `x - y`.
    Sub,
    /// The equality operator `x == y`.
    Eq,
    /// The inequality operator `x != y`.
    Neq,
    /// The less-than operator `x < y`.
    Lt,
    /// The less-than-or-equal operator `x <= y`.
    Leq,
    /// The greater-than operator `x > y`.
    Gt,
    /// The greater-than-or-equal operator `x >= y`.
    Geq,
    /// The logic and operator `x && y`.
    LogicAnd,
    /// The logic or operator `x || y`.
    LogicOr,
}

impl HasDesc for BinaryOp {
    fn desc(&self) -> &'static str {
        match *self {
            BinaryOp::Add => "`+` operator",
            BinaryOp::Sub => "`-` operator",
            BinaryOp::Eq => "`==` operator",
            BinaryOp::Neq => "`!=` operator",
            BinaryOp::Lt => "`<` operator",
            BinaryOp::Leq => "`<=` operator",
            BinaryOp::Gt => "`>` operator",
            BinaryOp::Geq => "`>=` operator",
            BinaryOp::LogicAnd => "`&&` operator",
            BinaryOp::LogicOr => "`||` operator",
        }
    }
}

/// A variable declaration.
#[derive(Debug, PartialEq, Eq)]
pub struct VarDecl {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    pub ty: NodeId,
    pub init: Option<NodeId>,
}

impl HasSpan for VarDecl {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for VarDecl {
    fn desc(&self) -> &'static str {
        "variable declaration"
    }

    fn desc_full(&self) -> String {
        format!("variable `{}`", self.name.value)
    }
}

/// A procedure.
#[derive(Debug, PartialEq, Eq)]
pub struct Proc {
    pub id: NodeId,
    pub span: Span,
    pub kind: ast::ProcedureKind,
    pub stmt: NodeId,
}

impl HasSpan for Proc {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Proc {
    fn desc(&self) -> &'static str {
        match self.kind {
            ast::ProcedureKind::Initial => "`initial` procedure",
            ast::ProcedureKind::Always => "`always` procedure",
            ast::ProcedureKind::AlwaysComb => "`always_comb` procedure",
            ast::ProcedureKind::AlwaysLatch => "`always_latch` procedure",
            ast::ProcedureKind::AlwaysFf => "`always_ff` procedure",
            ast::ProcedureKind::Final => "`final` procedure",
        }
    }
}

/// A variable declaration.
#[derive(Debug, PartialEq, Eq)]
pub struct Stmt {
    pub id: NodeId,
    pub label: Option<Spanned<Name>>,
    pub span: Span,
    pub kind: StmtKind,
}

impl HasSpan for Stmt {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.label.map(|l| l.span).unwrap_or(self.span)
    }
}

impl HasDesc for Stmt {
    fn desc(&self) -> &'static str {
        #[allow(unreachable_patterns)]
        match self.kind {
            StmtKind::Null => "null statement",
            StmtKind::Block(_) => "block",
            StmtKind::Assign { .. } => "assign statement",
            _ => "statement",
        }
    }
}

/// The different forms a statement can take.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtKind {
    /// A null statement.
    Null,
    /// A sequential block.
    Block(Vec<NodeId>),
    /// An assign statement (blocking or non-blocking).
    Assign {
        lhs: NodeId,
        rhs: NodeId,
        kind: AssignKind,
    },
    /// A statement with timing control.
    Timed {
        control: TimingControl,
        stmt: NodeId,
    },
    /// An expression statement.
    Expr(NodeId),
    /// An if statement.
    ///
    /// ```text
    /// if (<cond>) <main_stmt> [else <else_stmt>]
    /// ```
    If {
        cond: NodeId,
        main_stmt: NodeId,
        else_stmt: Option<NodeId>,
    },
    /// A loop statement.
    Loop { kind: LoopKind, body: NodeId },
}

/// The different forms an assignment can take.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignKind {
    /// A blocking assignment.
    Block(ast::AssignOp),
}

/// The different forms a loop can take.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopKind {
    /// A `forever` loop.
    Forever,
    /// A `repeat (<count>)` loop.
    Repeat(NodeId),
    //// A `while (<cond>)` loop.
    While(NodeId),
    //// A `do .. while (<cond>)` loop.
    Do(NodeId),
    //// A `for (<init>; <cond>; <step>)` loop.
    For(NodeId, NodeId, NodeId),
}

/// The different forms of timing control that can be applied to a statement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimingControl {
    /// A delayed statement. Contains an expression that evaluates to a time.
    Delay(NodeId),
    /// A statement triggered by any event on its inputs.
    ImplicitEvent,
    /// A statement triggered by an explicit event expression.
    ExplicitEvent(NodeId),
}

/// An event expression.
///
/// Contains multiple events separated by `,` or `or`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventExpr {
    pub id: NodeId,
    pub span: Span,
    pub events: Vec<Event>,
}

impl HasSpan for EventExpr {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for EventExpr {
    fn desc(&self) -> &'static str {
        "event expression"
    }
}

/// An individual event within an event expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Event {
    pub span: Span,
    pub edge: ast::EdgeIdent,
    pub expr: NodeId,
    pub iff: Vec<NodeId>,
}

/// A generate statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gen {
    pub id: NodeId,
    pub span: Span,
    pub kind: GenKind,
}

impl HasSpan for Gen {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Gen {
    fn desc(&self) -> &'static str {
        "generate statement"
    }
}

/// The different forms a generate statement can take.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenKind {
    /// An if-generate statement.
    If {
        cond: NodeId,
        main_body: NodeId,
        else_body: Option<NodeId>,
    },
    /// A for-generate statement.
    For {
        init: NodeId,
        cond: NodeId,
        step: NodeId,
        body: NodeId,
    },
}
