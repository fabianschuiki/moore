// Copyright (c) 2016-2021 Fabian Schuiki

//! This module contains the nodes of the tree structure that is the HIR.

use crate::crate_prelude::*;
use bit_vec::BitVec;
use num::{BigInt, BigRational};
use std::ops::Deref;

// Re-export the ports as part of the HIR.
pub use crate::port_list::{ExtPort, ExtPortExpr, ExtPortSelect, IntPort, IntPortData, PortList};

/// A reference to an HIR node.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum HirNode<'a> {
    Module(&'a Module<'a>),
    Interface(&'a Interface<'a>),
    IntPort(&'a IntPort<'a>),
    ExtPort(&'a ExtPort<'a>),
    Type(&'a Type),
    Expr(&'a Expr<'a>),
    InstTarget(&'a InstTarget<'a>),
    Inst(&'a Inst<'a>),
    TypeParam(&'a TypeParam),
    ValueParam(&'a ValueParam),
    VarDecl(&'a VarDecl),
    Proc(&'a Proc),
    Stmt(&'a Stmt<'a>),
    EventExpr(&'a EventExpr),
    Gen(&'a Gen),
    GenvarDecl(&'a GenvarDecl),
    Typedef(&'a Typedef),
    Assign(&'a Assign),
    Package(&'a Package),
    EnumVariant(&'a EnumVariant),
    SubroutinePort(&'a ast::SubroutinePort<'a>),
    CallArg(&'a ast::CallArg<'a>),
}

impl<'hir> HasSpan for HirNode<'hir> {
    fn span(&self) -> Span {
        match *self {
            HirNode::Module(x) => x.span(),
            HirNode::Interface(x) => x.span(),
            HirNode::IntPort(x) => x.span(),
            HirNode::ExtPort(x) => x.span(),
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
            HirNode::GenvarDecl(x) => x.span(),
            HirNode::Typedef(x) => x.span(),
            HirNode::Assign(x) => x.span(),
            HirNode::Package(x) => x.span(),
            HirNode::EnumVariant(x) => x.span(),
            HirNode::SubroutinePort(x) => x.span(),
            HirNode::CallArg(x) => x.span(),
        }
    }

    fn human_span(&self) -> Span {
        match *self {
            HirNode::Module(x) => x.human_span(),
            HirNode::Interface(x) => x.human_span(),
            HirNode::IntPort(x) => x.human_span(),
            HirNode::ExtPort(x) => x.human_span(),
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
            HirNode::GenvarDecl(x) => x.human_span(),
            HirNode::Typedef(x) => x.human_span(),
            HirNode::Assign(x) => x.human_span(),
            HirNode::Package(x) => x.human_span(),
            HirNode::EnumVariant(x) => x.human_span(),
            HirNode::SubroutinePort(x) => x.human_span(),
            HirNode::CallArg(x) => x.human_span(),
        }
    }
}

impl<'hir> HasDesc for HirNode<'hir> {
    fn desc(&self) -> &'static str {
        match *self {
            HirNode::Module(x) => x.desc(),
            HirNode::Interface(x) => x.desc(),
            HirNode::IntPort(x) => x.desc(),
            HirNode::ExtPort(x) => x.desc(),
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
            HirNode::GenvarDecl(x) => x.desc(),
            HirNode::Typedef(x) => x.desc(),
            HirNode::Assign(x) => x.desc(),
            HirNode::Package(x) => x.desc(),
            HirNode::EnumVariant(x) => x.desc(),
            HirNode::SubroutinePort(..) => "subroutine port",
            HirNode::CallArg(..) => "call argument",
        }
    }

    fn desc_full(&self) -> String {
        match *self {
            HirNode::Module(x) => x.desc_full(),
            HirNode::Interface(x) => x.desc_full(),
            HirNode::IntPort(x) => x.desc_full(),
            HirNode::ExtPort(x) => x.desc_full(),
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
            HirNode::GenvarDecl(x) => x.desc_full(),
            HirNode::Typedef(x) => x.desc_full(),
            HirNode::Assign(x) => x.desc_full(),
            HirNode::Package(x) => x.desc_full(),
            HirNode::EnumVariant(x) => x.desc_full(),
            HirNode::SubroutinePort(x) => x.to_string(),
            HirNode::CallArg(x) => x.to_string(),
        }
    }
}

/// A module.
#[derive(Debug, PartialEq, Eq)]
pub struct Module<'a> {
    /// The AST node.
    pub ast: &'a ast::Module<'a>,
    /// The ports of the module.
    pub ports_new: &'a PortList<'a>,
    /// The parameters of the module.
    pub params: &'a [NodeId],
    /// The contents of the module.
    pub block: ModuleBlock,
    /// The bottom of the name scope tree.
    pub last_rib: NodeId,
}

impl<'a> Deref for Module<'a> {
    type Target = &'a ast::Module<'a>;

    fn deref(&self) -> &Self::Target {
        &self.ast
    }
}

impl HasSpan for Module<'_> {
    fn span(&self) -> Span {
        self.ast.span
    }

    fn human_span(&self) -> Span {
        self.ast.name.span
    }
}

impl HasDesc for Module<'_> {
    fn desc(&self) -> &'static str {
        "module"
    }

    fn desc_full(&self) -> String {
        format!("module `{}`", self.ast.name)
    }
}

/// The contents of a module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleBlock {
    /// The module/interface instances in the module.
    pub insts: Vec<NodeId>,
    /// The variable and net declarations in the module.
    pub decls: Vec<NodeId>,
    /// The procedures in the module.
    pub procs: Vec<NodeId>,
    /// The generate blocks in the module.
    pub gens: Vec<NodeId>,
    /// The parameter declarations in the module.
    pub params: Vec<NodeId>,
    /// The continuous assignments in the module.
    pub assigns: Vec<NodeId>,
    /// The bottom of the name scope tree.
    pub last_rib: NodeId,
}

/// An instantiation target.
///
/// In an instantiation `foo #(...) a(), b(), c();` this struct represents the
/// `foo #(...)` part. Multiple instantiations (`a()`, `b()`, `c()`) may share
/// the same target.
#[derive(Debug, PartialEq, Eq)]
pub struct InstTarget<'a> {
    /// The underlying AST node.
    pub ast: &'a ast::Inst<'a>,
    /// The positional parameters.
    pub pos_params: Vec<PosParam>,
    /// The named parameters.
    pub named_params: Vec<NamedParam>,
}

impl<'a> Deref for InstTarget<'a> {
    type Target = &'a ast::Inst<'a>;

    fn deref(&self) -> &Self::Target {
        &self.ast
    }
}

impl HasSpan for InstTarget<'_> {
    fn span(&self) -> Span {
        self.ast.span
    }

    fn human_span(&self) -> Span {
        self.ast.target.span
    }
}

impl HasDesc for InstTarget<'_> {
    fn desc(&self) -> &'static str {
        "instantiation"
    }

    fn desc_full(&self) -> String {
        format!("`{}` instantiation", self.target)
    }
}

/// A positional parameter.
pub type PosParam = (Span, Option<NodeId>);

/// A named parameter.
pub type NamedParam = (Span, Spanned<Name>, Option<NodeId>);

/// An instantiation.
///
/// In an instantiation `foo #(...) a(), b(), c();`, this struct represents the
/// `a()` part.
#[derive(Debug, PartialEq, Eq)]
pub struct Inst<'a> {
    /// The underlying AST node.
    pub ast: &'a ast::InstName<'a>,
    /// The target of the instantiation.
    pub target: NodeId,
    /// The positional port connections.
    pub pos_ports: Vec<PosParam>,
    /// The named port connections.
    pub named_ports: Vec<NamedParam>,
    /// If the instantiation has a wildcard port connection `.*`.
    pub has_wildcard_port: bool,
}

impl<'a> Deref for Inst<'a> {
    type Target = &'a ast::InstName<'a>;

    fn deref(&self) -> &Self::Target {
        &self.ast
    }
}

impl HasSpan for Inst<'_> {
    fn span(&self) -> Span {
        self.ast.span
    }

    fn human_span(&self) -> Span {
        self.ast.name.span
    }
}

impl HasDesc for Inst<'_> {
    fn desc(&self) -> &'static str {
        "instance"
    }

    fn desc_full(&self) -> String {
        format!("instance `{}`", self.ast.name)
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

/// An interface.
#[derive(Debug, PartialEq, Eq)]
pub struct Interface<'a> {
    /// The AST node.
    pub ast: &'a ast::Interface<'a>,
    /// The ports of the interface.
    pub ports: &'a PortList<'a>,
    /// The contents of the interface.
    pub block: ModuleBlock,
}

impl<'a> Deref for Interface<'a> {
    type Target = &'a ast::Interface<'a>;

    fn deref(&self) -> &Self::Target {
        &self.ast
    }
}

impl HasSpan for Interface<'_> {
    fn span(&self) -> Span {
        self.ast.span
    }

    fn human_span(&self) -> Span {
        self.ast.name.span
    }
}

impl HasDesc for Interface<'_> {
    fn desc(&self) -> &'static str {
        "interface"
    }

    fn desc_full(&self) -> String {
        format!("interface `{}`", self.ast.name)
    }
}

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

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    pub id: NodeId,
    pub span: Span,
    pub kind: TypeKind,
}

impl Type {
    /// Check if this is an explicit type.
    pub fn is_explicit(&self) -> bool {
        !self.is_implicit()
    }

    /// Check if this is an implicit type.
    pub fn is_implicit(&self) -> bool {
        self.kind == TypeKind::Implicit
    }
}

impl HasSpan for Type {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Type {
    fn desc(&self) -> &'static str {
        self.kind.desc()
    }

    fn desc_full(&self) -> String {
        self.kind.desc_full()
    }
}

/// The different forms a type can take.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    /// An implicit type.
    Implicit,
    /// A builtin type.
    Builtin(BuiltinType),
    /// A named type.
    Named(Spanned<Name>),
    /// A struct or union type.
    Struct(Vec<NodeId>),
    /// A packed array such as `bit [31:0]`.
    ///
    /// Represented as `(inner_type, range_lhs, range_rhs)`.
    PackedArray(Box<TypeKind>, NodeId, NodeId),
    /// A scope access such as `foo::bar`.
    Scope(NodeId, Spanned<Name>),
    /// An enum type.
    ///
    /// Each element in the vector refers to a `EnumVariant`. The optional field
    /// indicates the representation type.
    Enum(Vec<(Spanned<Name>, NodeId)>, Option<NodeId>),
    /// A type reference on an expression, such as `type(x)`.
    RefExpr(NodeId),
    /// A type reference on a type, such as `type(int)`.
    RefType(NodeId),
}

impl HasDesc for TypeKind {
    fn desc(&self) -> &'static str {
        #[allow(unreachable_patterns)]
        match *self {
            TypeKind::Implicit => "implicit type",
            TypeKind::Builtin(BuiltinType::Void) => "void type",
            TypeKind::Builtin(BuiltinType::Bit) => "bit type",
            TypeKind::Builtin(BuiltinType::Logic) => "logic type",
            TypeKind::Builtin(BuiltinType::Byte) => "byte type",
            TypeKind::Builtin(BuiltinType::ShortInt) => "short int type",
            TypeKind::Builtin(BuiltinType::Int) => "int type",
            TypeKind::Builtin(BuiltinType::Integer) => "integer type",
            TypeKind::Builtin(BuiltinType::LongInt) => "long int type",
            TypeKind::Struct(_) => "struct type",
            TypeKind::PackedArray(..) => "packed array type",
            _ => "type",
        }
    }

    fn desc_full(&self) -> String {
        match *self {
            TypeKind::Named(n) => format!("type `{}`", n.value),
            _ => self.desc().into(),
        }
    }
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
    Integer,
    LongInt,
    Time,
    String,
}

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr<'a> {
    /// The AST node.
    pub ast: &'a ast::Expr<'a>,
    /// The specific expression data.
    pub kind: ExprKind<'a>,
}

impl<'a> Deref for Expr<'a> {
    type Target = &'a ast::Expr<'a>;

    fn deref(&self) -> &Self::Target {
        &self.ast
    }
}

impl HasSpan for Expr<'_> {
    fn span(&self) -> Span {
        self.ast.span()
    }

    fn human_span(&self) -> Span {
        self.ast.human_span()
    }
}

impl HasDesc for Expr<'_> {
    fn desc(&self) -> &'static str {
        #[allow(unreachable_patterns)]
        match self.kind {
            ExprKind::IntConst { .. } => "integer constant",
            ExprKind::TimeConst(_) => "time constant",
            ExprKind::Ident(_) => "identifier",
            _ => "expression",
        }
    }

    fn desc_full(&self) -> String {
        #[allow(unreachable_patterns)]
        match self.kind {
            ExprKind::IntConst { value: ref k, .. } => format!("{} `{}`", self.desc(), k),
            ExprKind::TimeConst(ref k) => format!("{} `{}`", self.desc(), k),
            ExprKind::Ident(n) => format!("`{}`", n.value),
            ExprKind::PositionalPattern(..) => format!("positional pattern"),
            ExprKind::NamedPattern(..) => format!("named pattern"),
            ExprKind::RepeatPattern(..) => format!("repeat pattern"),
            _ => format!("{} `{}`", self.desc(), self.span().extract()),
        }
    }
}

/// The different forms an expression can take.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind<'a> {
    /// An integer constant literal such as `42` or `'d42` or `32'd42`.
    ///
    /// The `special_bits` mask keeps track of which bits in the number are `x`
    /// or `z`. The `x_bits` mask tracks which of these special bits are `x`.
    IntConst {
        width: usize,
        value: BigInt,
        signed: bool,
        special_bits: BitVec,
        x_bits: BitVec,
    },
    /// An unsized and unbased constant literal such as `'0`.
    UnsizedConst(char),
    /// A time constant literal.
    TimeConst(BigRational),
    /// A string constant literal.
    StringConst(Spanned<Name>),
    /// An identifier.
    Ident(Spanned<Name>),
    /// A unary operator.
    Unary(UnaryOp, NodeId),
    /// A binary operator.
    Binary(BinaryOp, NodeId, NodeId),
    /// A field access such as `a.b`.
    Field(NodeId, Spanned<Name>),
    /// An index access such as `a[b]` or `a[b:c]`.
    Index(NodeId, IndexMode),
    /// A builtin function call such as `$clog2(x)`.
    Builtin(BuiltinCall<'a>),
    /// A ternary expression such as `a ? b : c`.
    Ternary(NodeId, NodeId, NodeId),
    /// A scope expression such as `foo::bar`.
    Scope(NodeId, Spanned<Name>),
    /// A positional pattern such as `'{a, b, c}`.
    PositionalPattern(Vec<NodeId>),
    /// A named pattern such as `'{logic: a, foo: b, 31: c, default: d}`.
    NamedPattern(Vec<(PatternMapping, NodeId)>),
    /// A repeat pattern such as `'{32{a, b, c}}`.
    RepeatPattern(NodeId, Vec<NodeId>),
    /// A concatenation such as `{a,b}` or `{4{a,b}}`.
    Concat(Option<NodeId>, Vec<NodeId>),
    /// A cast `(ty, expr)` such as `foo'(bar)`.
    Cast(NodeId, NodeId),
    /// A sign cast such as `unsigned'(foo)`.
    CastSign(Spanned<ty::Sign>, NodeId),
    /// A size cast `(size_expr, expr)` such as `42'(foo)`.
    CastSize(NodeId, NodeId),
    /// An inside expression such as `a inside {b, c}`.
    Inside(NodeId, Vec<Spanned<InsideRange>>),
    /// A function call such as `foo(a, b, c)`.
    FunctionCall(&'a ast::SubroutineDecl<'a>, &'a [ast::CallArg<'a>]),
    /// An assignment.
    Assign {
        op: ast::AssignOp,
        lhs: &'a ast::Expr<'a>,
        rhs: &'a ast::Expr<'a>,
    },
    /// An expression in the AST that requires no representational change.
    Ast(&'a ast::Expr<'a>),
}

/// The different unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// The plus operator `+x`.
    Pos,
    /// The minus operator `-x`.
    Neg,
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
    /// The reduction and operator `&x`.
    RedAnd,
    /// The reduction not-and operator `~&x`.
    RedNand,
    /// The reduction or operator `|x`.
    RedOr,
    /// The reduction not-or operator `~|x`.
    RedNor,
    /// The reduction exclusive-or operator `^x`.
    RedXor,
    /// The reduction exclusive-not-or operator `^~x` or `~^x`.
    RedXnor,
}

impl HasDesc for UnaryOp {
    fn desc(&self) -> &'static str {
        match *self {
            UnaryOp::Pos => "unary `+` operator",
            UnaryOp::Neg => "unary `-` operator",
            UnaryOp::BitNot => "`~` operator",
            UnaryOp::LogicNot => "`!` operator",
            UnaryOp::PreInc => "`++` prefix operator",
            UnaryOp::PreDec => "`--` prefix operator",
            UnaryOp::PostInc => "`++` postfix operator",
            UnaryOp::PostDec => "`--` postfix operator",
            UnaryOp::RedAnd => "`&` reduction operator",
            UnaryOp::RedNand => "`~&` reduction operator",
            UnaryOp::RedOr => "`|` reduction operator",
            UnaryOp::RedNor => "`~|` reduction operator",
            UnaryOp::RedXor => "`^` reduction operator",
            UnaryOp::RedXnor => "`^~` reduction operator",
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
    /// The multiplication operator `x * y`.
    Mul,
    /// The division operator `x / y`.
    Div,
    /// The modulus operator `x % y`.
    Mod,
    /// The power operator `x ** y`.
    Pow,
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
    /// The bitwise and operator `x & y`.
    BitAnd,
    /// The bitwise not-and operator `x ~& y`.
    BitNand,
    /// The bitwise or operator `x | y`.
    BitOr,
    /// The bitwise not-or operator `x ~| y`.
    BitNor,
    /// The bitwise exclusive-or operator `x ^ y`.
    BitXor,
    /// The bitwise exclusive-not-or operator `x ^~ y` or `x ~^ y`.
    BitXnor,
    /// The logic left shift operator `x << y`.
    LogicShL,
    /// The logic right shift operator `x >> y`.
    LogicShR,
    /// The arithmetic left shift operator `x <<< y`.
    ArithShL,
    /// The arithmetic right shift operator `x >>> y`.
    ArithShR,
}

impl HasDesc for BinaryOp {
    fn desc(&self) -> &'static str {
        match *self {
            BinaryOp::Add => "`+` operator",
            BinaryOp::Sub => "`-` operator",
            BinaryOp::Mul => "`*` operator",
            BinaryOp::Div => "`/` operator",
            BinaryOp::Mod => "`%` operator",
            BinaryOp::Pow => "`**` operator",
            BinaryOp::Eq => "`==` operator",
            BinaryOp::Neq => "`!=` operator",
            BinaryOp::Lt => "`<` operator",
            BinaryOp::Leq => "`<=` operator",
            BinaryOp::Gt => "`>` operator",
            BinaryOp::Geq => "`>=` operator",
            BinaryOp::LogicAnd => "`&&` operator",
            BinaryOp::LogicOr => "`||` operator",
            BinaryOp::BitAnd => "`&` operator",
            BinaryOp::BitNand => "`~&` operator",
            BinaryOp::BitOr => "`|` operator",
            BinaryOp::BitNor => "`~|` operator",
            BinaryOp::BitXor => "`^` operator",
            BinaryOp::BitXnor => "`~^` operator",
            BinaryOp::LogicShL => "`<<` operator",
            BinaryOp::LogicShR => "`>>` operator",
            BinaryOp::ArithShL => "`<<<` operator",
            BinaryOp::ArithShR => "`>>>` operator",
        }
    }
}

/// The different forms an index expression can take.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IndexMode {
    /// A single value access such as `[a]`.
    One(NodeId),
    /// A slice of values such as `[a:b]`, `[a+:b]`, or `[a-:b]`.
    Many(ast::RangeMode, NodeId, NodeId),
}

/// The different builtin function calls that are supported.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinCall<'a> {
    /// An unsupported builtin. Will yield constant 0.
    Unsupported,
    /// A call to the ceil-log2 function `$clog2(x)`.
    Clog2(NodeId),
    /// A call to the storage size function `$bits(x)`.
    Bits(&'a ast::TypeOrExpr<'a>),
    /// A call to the convert-to-signed function `$signed(x)`.
    Signed(NodeId),
    /// A call to the convert-to-unsigned function `$unsigned(x)`.
    Unsigned(NodeId),
    /// A call to the `$countones(x)` function.
    CountOnes(&'a ast::Expr<'a>),
    /// A call to the `$onehot(x)` function.
    OneHot(&'a ast::Expr<'a>),
    /// A call to the `$onehot0(x)` function.
    OneHot0(&'a ast::Expr<'a>),
    /// A call to the `$isunknown(x)` function.
    IsUnknown(&'a ast::Expr<'a>),
    /// A call to one of the array dimension functions.
    ArrayDim(ArrayDim, &'a ast::Expr<'a>, Option<&'a ast::Expr<'a>>),
}

/// The different builtin array dimension function calls that are supported.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArrayDim {
    /// The `$left` function.
    Left,
    /// The `$right` function.
    Right,
    /// The `$low` function.
    Low,
    /// The `$high` function.
    High,
    /// The `$increment` function.
    Increment,
    /// The `$size` function.
    Size,
}

/// A variable or net declaration.
#[derive(Debug, PartialEq, Eq)]
pub struct VarDecl {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    /// Data type
    pub ty: NodeId,
    /// Initial value
    pub init: Option<NodeId>,
    /// Variable or net-specific data
    pub kind: ast::VarKind,
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
        match self.kind {
            ast::VarKind::Var => "variable declaration",
            ast::VarKind::Net { .. } => "net declaration",
        }
    }

    fn desc_full(&self) -> String {
        match self.kind {
            ast::VarKind::Var => format!("variable `{}`", self.name.value),
            ast::VarKind::Net { .. } => format!("net `{}`", self.name.value),
        }
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
pub struct Stmt<'a> {
    pub id: NodeId,
    pub label: Option<Spanned<Name>>,
    pub span: Span,
    pub kind: StmtKind<'a>,
}

impl HasSpan for Stmt<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.label.map(|l| l.span).unwrap_or(self.span)
    }
}

impl HasDesc for Stmt<'_> {
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
pub enum StmtKind<'a> {
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
    /// An inline group of statements.
    ///
    /// This is a special node that is used for example with variable
    /// declarations, where one statement can generate multiple nodes referrable
    /// by name. An inline group differs from a block in that its ribs are
    /// made visible, whereas a block keeps them local.
    InlineGroup { stmts: Vec<NodeId>, rib: NodeId },
    /// A case statement.
    Case {
        expr: NodeId,
        ways: Vec<(Vec<NodeId>, NodeId)>,
        default: Option<NodeId>,
        kind: ast::CaseKind,
    },
    /// A statement in the AST that requires no representational change.
    Ast(&'a ast::Stmt<'a>),
}

/// The different forms an assignment can take.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssignKind {
    /// A blocking assignment.
    Block(ast::AssignOp),
    /// A non-blocking assignment.
    Nonblock,
    /// A non-blocking assignment with delay.
    NonblockDelay(NodeId),
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
        main_body: ModuleBlock,
        else_body: Option<ModuleBlock>,
    },
    /// A for-generate statement.
    For {
        init: Vec<NodeId>,
        cond: NodeId,
        step: NodeId,
        body: ModuleBlock,
    },
}

/// A genvar declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenvarDecl {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    pub init: Option<NodeId>,
}

impl HasSpan for GenvarDecl {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for GenvarDecl {
    fn desc(&self) -> &'static str {
        "genvar declaration"
    }

    fn desc_full(&self) -> String {
        format!("genvar `{}`", self.name.value)
    }
}

/// A typedef.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Typedef {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    pub ty: NodeId,
}

impl HasSpan for Typedef {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for Typedef {
    fn desc(&self) -> &'static str {
        "typedef"
    }

    fn desc_full(&self) -> String {
        format!("typedef `{}`", self.name.value)
    }
}

/// A continuous assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assign {
    pub id: NodeId,
    pub span: Span,
    pub lhs: NodeId,
    pub rhs: NodeId,
}

impl HasSpan for Assign {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Assign {
    fn desc(&self) -> &'static str {
        "assignment"
    }
}

/// A package.
#[derive(Debug, PartialEq, Eq)]
pub struct Package {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    /// The names declared in this package.
    pub names: Vec<(Spanned<Name>, NodeId)>,
    /// The constant declarations in the module.
    pub decls: Vec<NodeId>,
    /// The parameter declarations in the package.
    pub params: Vec<NodeId>,
    /// The bottom of the name scope tree.
    pub last_rib: NodeId,
}

impl HasSpan for Package {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for Package {
    fn desc(&self) -> &'static str {
        "package"
    }

    fn desc_full(&self) -> String {
        format!("package `{}`", self.name.value)
    }
}

/// A single variant of an enum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumVariant {
    pub id: NodeId,
    pub name: Spanned<Name>,
    pub span: Span,
    /// The enum type declaration that contains this variant.
    pub enum_id: NodeId,
    /// The index of the variant within the enum.
    pub index: usize,
    /// The optional expression that explicitly assigns a value to the variant.
    pub value: Option<NodeId>,
}

impl HasSpan for EnumVariant {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for EnumVariant {
    fn desc(&self) -> &'static str {
        "enum variant"
    }

    fn desc_full(&self) -> String {
        format!("enum variant `{}`", self.name.value)
    }
}

/// A named pattern mapping.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PatternMapping {
    /// A field with a type as key, e.g. `'{logic: ...}`.
    Type(NodeId),
    /// A field with an expression as key, e.g. `'{foo: ..., 31: ...}`.
    Member(NodeId),
    /// A default field, e.g. `'{default: ...}`.
    Default,
}

/// Single values or value ranges admissible in `inside` sets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InsideRange {
    Single(NodeId),
    Range(NodeId, NodeId),
}
