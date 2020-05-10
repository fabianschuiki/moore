// Copyright (c) 2016-2020 Fabian Schuiki

#![allow(unused_variables)]

use crate::token::{Lit, Op};
use moore_common::{
    name::Name,
    source::{Span, Spanned, INVALID_SPAN},
    util::{HasDesc, HasSpan},
};
use moore_derive::CommonNode;
use std::cell::Cell;

/// Common denominator across all AST nodes.
pub struct Node<'a, T> {
    /// Full span the node covers in the input.
    pub span: Span,
    /// Parent node.
    pub parent: Cell<Option<&'a ()>>,
    /// Lexical predecessor node.
    pub lex_pred: Cell<Option<&'a ()>>,
    /// Lexical successor node.
    pub lex_succ: Cell<Option<&'a ()>>,
    /// Per-node data.
    pub data: T,
}

/// Common interface to all AST nodes.
pub trait CommonNode {
    /// Apply a function to each child node.
    fn for_each_child(&self, f: &mut dyn FnMut(&dyn CommonNode));
}

pub use self::ExprData::*;
pub use self::StmtData::*;
pub use self::TypeData::*;

#[derive(Debug, PartialEq, Eq)]
pub struct Root {
    pub timeunits: Timeunit,
    pub items: Vec<Item>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModDecl {
    pub span: Span,
    pub lifetime: Lifetime, // default static
    pub name: Name,
    pub name_span: Span,
    pub imports: Vec<ImportDecl>,
    pub params: Vec<ParamDecl>,
    pub ports: Vec<Port>,
    pub items: Vec<Item>,
}

impl HasSpan for ModDecl {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name_span
    }
}

impl HasDesc for ModDecl {
    fn desc(&self) -> &'static str {
        "module declaration"
    }

    fn desc_full(&self) -> String {
        format!("module `{}`", self.name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntfDecl {
    pub span: Span,
    pub lifetime: Lifetime, // default static
    pub name: Name,
    pub name_span: Span,
    pub params: Vec<ParamDecl>,
    pub ports: Vec<Port>,
    pub items: Vec<Item>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageDecl {
    pub span: Span,
    pub lifetime: Lifetime,
    pub name: Name,
    pub name_span: Span,
    pub timeunits: Timeunit,
    pub items: Vec<Item>,
}

impl HasSpan for PackageDecl {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name_span
    }
}

impl HasDesc for PackageDecl {
    fn desc(&self) -> &'static str {
        "package declaration"
    }

    fn desc_full(&self) -> String {
        format!("package `{}`", self.name)
    }
}

/// Lifetime specifier for variables, tasks, and functions. Defaults to static.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Lifetime {
    Static,
    Automatic,
}

/// A time unit specification.
///
/// ```text
/// "timeunit" time_literal ["/" time_literal] ";"
/// "timeprecision" time_literal ";"
/// ```
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Timeunit {
    pub unit: Option<Spanned<Lit>>,
    pub prec: Option<Spanned<Lit>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Item {
    Dummy,
    ModuleDecl(ModDecl),
    InterfaceDecl(IntfDecl),
    PackageDecl(PackageDecl),
    ClassDecl(ClassDecl),
    ProgramDecl(()),
    ImportDecl(ImportDecl),
    ParamDecl(ParamDecl),
    ModportDecl(ModportDecl),
    Typedef(Typedef),
    PortDecl(PortDecl),
    Procedure(Procedure),
    SubroutineDecl(SubroutineDecl),
    ContAssign(ContAssign),
    GenvarDecl(Vec<GenvarDecl>),
    GenerateRegion(Span, Vec<Item>),
    GenerateFor(GenerateFor),
    GenerateIf(GenerateIf),
    GenerateCase(GenerateCase),
    Assertion(Assertion),
    NetDecl(NetDecl),
    VarDecl(VarDecl),
    Inst(Inst),
}

impl HasSpan for Item {
    fn span(&self) -> Span {
        match *self {
            Item::ModuleDecl(ref decl) => decl.span(),
            Item::InterfaceDecl(ref decl) => decl.span,
            Item::PackageDecl(ref decl) => decl.span,
            Item::ImportDecl(ref decl) => decl.span,
            Item::ParamDecl(ref decl) => decl.span,
            Item::ProgramDecl(ref decl) => INVALID_SPAN,
            Item::ModportDecl(ref decl) => decl.span,
            Item::ClassDecl(ref decl) => decl.span,
            Item::PortDecl(ref decl) => decl.span,
            Item::Procedure(ref prc) => prc.span,
            Item::SubroutineDecl(ref decl) => decl.span,
            Item::Assertion(ref assertion) => assertion.span,
            Item::NetDecl(ref decl) => decl.span,
            Item::VarDecl(ref decl) => decl.span,
            Item::Inst(ref inst) => inst.span,
            _ => INVALID_SPAN,
        }
    }

    fn human_span(&self) -> Span {
        match *self {
            Item::ModuleDecl(ref decl) => decl.human_span(),
            _ => self.span(),
        }
    }
}

impl HasDesc for Item {
    fn desc(&self) -> &'static str {
        match *self {
            Item::ModuleDecl(ref decl) => decl.desc(),
            Item::InterfaceDecl(ref decl) => "interface declaration",
            Item::PackageDecl(ref decl) => "package declaration",
            Item::ImportDecl(ref decl) => "import declaration",
            Item::ParamDecl(ref decl) => "parameter declaration",
            Item::ProgramDecl(ref decl) => "program declaration",
            Item::ModportDecl(ref decl) => "modport declaration",
            Item::ClassDecl(ref decl) => "class declaration",
            Item::PortDecl(ref decl) => "port declaration",
            Item::Procedure(ref prc) => "procedure declaration",
            Item::SubroutineDecl(ref decl) => "subroutine declaration",
            Item::Assertion(ref assertion) => "assertion",
            Item::NetDecl(ref decl) => "net declaration",
            Item::VarDecl(ref decl) => "variable declaration",
            Item::Inst(ref inst) => "instantiation",
            _ => "<invalid item>",
        }
    }

    fn desc_full(&self) -> String {
        match *self {
            Item::ModuleDecl(ref decl) => decl.desc_full(),
            _ => self.desc().into(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type {
    pub span: Span,
    pub data: TypeData,
    pub sign: TypeSign,
    pub dims: Vec<TypeDim>,
}

impl HasSpan for Type {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Type {
    fn desc(&self) -> &'static str {
        match self.data {
            ImplicitType => "implicit type",
            _ => "type",
        }
    }

    fn desc_full(&self) -> String {
        match self.data {
            ImplicitType => self.desc().into(),
            _ => format!("type `{}`", self.span().extract()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeData {
    ImplicitType,
    VoidType,
    NamedType(Identifier),
    StringType,
    ChandleType,
    VirtIntfType(Name),
    EventType,
    MailboxType,
    ImplicitSignedType,
    ImplicitUnsignedType,

    // Scoping
    ScopedType {
        ty: Box<Type>,
        member: bool,
        name: Identifier,
    },

    // Integer Vector Types
    BitType,
    LogicType,
    RegType,

    // Integer Atom Types
    ByteType,
    ShortIntType,
    IntType,
    IntegerType,
    LongIntType,
    TimeType,

    // Non-integer Types
    ShortRealType,
    RealType,
    RealtimeType,

    // Enumerations
    EnumType(Option<Box<Type>>, Vec<EnumName>),
    StructType {
        kind: StructKind,
        packed: bool,
        signing: TypeSign,
        members: Vec<StructMember>,
    },

    // Specialization
    SpecializedType(Box<Type>, Vec<ParamAssignment>),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum TypeSign {
    None,
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDim {
    Expr(Expr),
    Range(Expr, Expr),
    Queue,
    Unsized,
    Associative,
}

impl HasDesc for TypeDim {
    fn desc(&self) -> &'static str {
        "type dimension"
    }

    fn desc_full(&self) -> String {
        match *self {
            TypeDim::Expr(ref expr) => format!("`[{}]`", expr.span().extract()),
            TypeDim::Range(ref lhs, ref rhs) => {
                format!("`[{}:{}]`", lhs.span().extract(), rhs.span().extract())
            }
            TypeDim::Queue => format!("`[$]`"),
            TypeDim::Unsized => format!("`[]`"),
            TypeDim::Associative => format!("associative type dimension"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumName {
    pub span: Span,
    pub name: Identifier,
    pub range: Option<Expr>,
    pub value: Option<Expr>,
}

impl HasSpan for EnumName {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for EnumName {
    fn desc(&self) -> &'static str {
        "enum variant"
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum StructKind {
    Struct,
    Union,
    TaggedUnion,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructMember {
    pub span: Span,
    pub rand_qualifier: Option<RandomQualifier>,
    pub ty: Box<Type>,
    pub names: Vec<VarDeclName>,
}

impl HasSpan for StructMember {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for StructMember {
    fn desc(&self) -> &'static str {
        "struct member"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Port {
    Intf {
        span: Span,
        modport: Option<Identifier>,
        name: Identifier,
        dims: Vec<TypeDim>,
        expr: Option<Expr>,
    },
    Explicit {
        span: Span,
        dir: Option<PortDir>,
        name: Identifier,
        expr: Option<Expr>,
    },
    Named {
        span: Span,
        dir: Option<PortDir>,
        kind: Option<PortKind>,
        ty: Type,
        name: Identifier,
        dims: Vec<TypeDim>,
        expr: Option<Expr>,
    },
    Implicit(Expr),
}

impl HasSpan for Port {
    fn span(&self) -> Span {
        match *self {
            Port::Intf { span, .. } => span,
            Port::Explicit { span, .. } => span,
            Port::Named { span, .. } => span,
            Port::Implicit(ref expr) => expr.span,
        }
    }

    fn human_span(&self) -> Span {
        match *self {
            Port::Intf { name, .. } => name.span,
            Port::Explicit { name, .. } => name.span,
            Port::Named { name, .. } => name.span,
            Port::Implicit(ref expr) => expr.span,
        }
    }
}

impl HasDesc for Port {
    fn desc(&self) -> &'static str {
        match *self {
            Port::Intf { name, .. } => "interface port",
            Port::Explicit { name, .. } => "explicit port",
            Port::Named { name, .. } => "port",
            Port::Implicit(ref expr) => "implicit port",
        }
    }

    fn desc_full(&self) -> String {
        match *self {
            Port::Intf { name, .. } | Port::Explicit { name, .. } | Port::Named { name, .. } => {
                format!("{} `{}`", self.desc(), name.name)
            }
            Port::Implicit(ref expr) => format!("{} `{}`", self.desc(), expr.span.extract()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortDecl {
    pub span: Span,
    pub dir: PortDir,
    pub kind: Option<PortKind>,
    pub ty: Type,
    pub names: Vec<VarDeclName>,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum PortKind {
    Net(NetType),
    Var,
}

impl std::fmt::Display for PortKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            PortKind::Net(nt) => write!(f, "{}", nt),
            PortKind::Var => write!(f, "var"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub enum PortDir {
    Input,
    Output,
    Inout,
    Ref,
}

impl std::fmt::Display for PortDir {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            PortDir::Input => write!(f, "input"),
            PortDir::Output => write!(f, "output"),
            PortDir::Inout => write!(f, "inout"),
            PortDir::Ref => write!(f, "ref"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum NetType {
    Supply0,
    Supply1,
    Tri,
    TriAnd,
    TriOr,
    TriReg,
    Tri0,
    Tri1,
    Uwire,
    Wire,
    WireAnd,
    WireOr,
}

impl std::fmt::Display for NetType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            NetType::Supply0 => write!(f, "supply0"),
            NetType::Supply1 => write!(f, "supply1"),
            NetType::Tri => write!(f, "tri"),
            NetType::TriAnd => write!(f, "triand"),
            NetType::TriOr => write!(f, "trior"),
            NetType::TriReg => write!(f, "trireg"),
            NetType::Tri0 => write!(f, "tri0"),
            NetType::Tri1 => write!(f, "tri1"),
            NetType::Uwire => write!(f, "uwire"),
            NetType::Wire => write!(f, "wire"),
            NetType::WireAnd => write!(f, "wand"),
            NetType::WireOr => write!(f, "wor"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Procedure {
    pub span: Span,
    pub kind: ProcedureKind,
    pub stmt: Stmt,
}

impl HasSpan for Procedure {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Procedure {
    fn desc(&self) -> &'static str {
        "procedure"
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum ProcedureKind {
    Initial,
    Always,
    AlwaysComb,
    AlwaysLatch,
    AlwaysFf,
    Final,
}

#[derive(CommonNode, Debug, Clone, PartialEq, Eq)]
pub struct Stmt {
    pub span: Span,
    #[ignore_child]
    pub label: Option<Name>,
    pub data: StmtData,
}

impl HasSpan for Stmt {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Stmt {
    fn desc(&self) -> &'static str {
        "statement"
    }
}

#[derive(CommonNode, Debug, Clone, PartialEq, Eq)]
pub enum StmtData {
    NullStmt,
    SequentialBlock(Vec<Stmt>),
    ParallelBlock(Vec<Stmt>, JoinKind),
    IfStmt {
        up: Option<UniquePriority>,
        cond: Expr,
        main_stmt: Box<Stmt>,
        else_stmt: Option<Box<Stmt>>,
    },
    BlockingAssignStmt {
        lhs: Expr,
        rhs: Expr,
        op: AssignOp,
    },
    NonblockingAssignStmt {
        lhs: Expr,
        rhs: Expr,
        delay: Option<DelayControl>,
        event: Option<()>,
    },
    TimedStmt(TimingControl, Box<Stmt>),
    CaseStmt {
        up: Option<UniquePriority>,
        kind: CaseKind,
        expr: Expr,
        mode: CaseMode,
        items: Vec<CaseItem>,
    },
    ForeverStmt(Box<Stmt>),
    RepeatStmt(Expr, Box<Stmt>),
    WhileStmt(Expr, Box<Stmt>),
    DoStmt(Box<Stmt>, Expr),
    ForStmt(Box<Stmt>, Expr, Expr, Box<Stmt>),
    ForeachStmt(Expr, Vec<Option<Identifier>>, Box<Stmt>),
    ExprStmt(Expr),
    VarDeclStmt(VarDecl),
    GenvarDeclStmt(Vec<GenvarDecl>),
    ContinueStmt,
    BreakStmt,
    ReturnStmt(Option<Expr>),
    ImportStmt(ImportDecl),
    AssertionStmt(Box<Assertion>),
    WaitExprStmt(Expr, Box<Stmt>),
    WaitForkStmt,
    DisableForkStmt,
    DisableStmt(Name),
}

impl Stmt {
    pub fn new_null(span: Span) -> Stmt {
        Stmt {
            span: span,
            label: None,
            data: NullStmt,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum JoinKind {
    All,
    Any,
    None,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum UniquePriority {
    Unique,
    Unique0,
    Priority,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum CaseKind {
    Normal,
    DontCareZ,
    DontCareXZ,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum CaseMode {
    Normal,
    Inside,
    Pattern,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaseItem {
    Default(Box<Stmt>),
    Expr(Vec<Expr>, Box<Stmt>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DelayControl {
    pub span: Span,
    pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventControl {
    pub span: Span,
    pub data: EventControlData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventControlData {
    Implicit,
    Expr(EventExpr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CycleDelay {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimingControl {
    Delay(DelayControl),
    Event(EventControl),
    Cycle(CycleDelay),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Identity,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    LogicShL,
    LogicShR,
    ArithShL,
    ArithShR,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDecl {
    pub span: Span,
    pub konst: bool,
    pub var: bool,
    pub lifetime: Option<Lifetime>,
    pub ty: Type,
    pub names: Vec<VarDeclName>,
}

impl HasSpan for VarDecl {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for VarDecl {
    fn desc(&self) -> &'static str {
        "variable declaration"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDeclName {
    pub span: Span,
    pub name: Name,
    pub name_span: Span,
    pub dims: Vec<TypeDim>,
    pub init: Option<Expr>,
}

impl HasSpan for VarDeclName {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name_span
    }
}

impl HasDesc for VarDeclName {
    fn desc(&self) -> &'static str {
        "variable"
    }

    fn desc_full(&self) -> String {
        format!("variable `{}`", self.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenvarDecl {
    pub span: Span,
    pub name: Name,
    pub name_span: Span,
    pub init: Option<Expr>,
}

impl HasSpan for GenvarDecl {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name_span
    }
}

impl HasDesc for GenvarDecl {
    fn desc(&self) -> &'static str {
        "genvar"
    }

    fn desc_full(&self) -> String {
        format!("genvar `{}`", self.name)
    }
}

// TODO: Assign an id to each and every expression. This will later allow the
// types of each expression to be recorded properly, and simplifies the act of
// assigning IDs. Maybe expression IDs should be distinct from node IDs?
#[derive(CommonNode, Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub span: Span,
    pub data: ExprData,
}

impl HasSpan for Expr {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Expr {
    fn desc(&self) -> &'static str {
        "expression"
    }
}

pub type Expr2<'a> = Node<'a, ExprData>;

impl HasSpan for Expr2<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Expr2<'_> {
    fn desc(&self) -> &'static str {
        "expression"
    }
}

#[derive(CommonNode, Debug, Clone, PartialEq, Eq)]
pub enum ExprData {
    DummyExpr,
    LiteralExpr(Lit),
    IdentExpr(Identifier),
    SysIdentExpr(Identifier),
    ScopeExpr(Box<Expr>, Identifier),
    IndexExpr {
        indexee: Box<Expr>,
        index: Box<Expr>,
    },
    UnaryExpr {
        op: Op,
        expr: Box<Expr>,
        postfix: bool,
    },
    BinaryExpr {
        op: Op,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    TernaryExpr {
        cond: Box<Expr>,
        true_expr: Box<Expr>,
        false_expr: Box<Expr>,
    },
    AssignExpr {
        op: AssignOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    CallExpr(Box<Expr>, Vec<CallArg>),
    TypeExpr(Box<Type>), // TODO: Check if this is still needed, otherwise remove
    ConstructorCallExpr(Vec<CallArg>),
    ClassNewExpr(Option<Box<Expr>>),
    ArrayNewExpr(Box<Expr>, Option<Box<Expr>>),
    EmptyQueueExpr,
    StreamConcatExpr {
        slice: Option<StreamConcatSlice>,
        exprs: Vec<StreamExpr>,
    },
    ConcatExpr {
        repeat: Option<Box<Expr>>,
        exprs: Vec<Expr>,
    },
    MinTypMaxExpr {
        min: Box<Expr>,
        typ: Box<Expr>,
        max: Box<Expr>,
    },
    RangeExpr {
        mode: RangeMode,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    MemberExpr {
        expr: Box<Expr>,
        name: Identifier,
    },
    PatternExpr(Vec<PatternField>),
    InsideExpr(Box<Expr>, Vec<ValueRange>),
    CastExpr(Type, Box<Expr>),
    CastSizeExpr(Box<Expr>, Box<Expr>),
    CastSignExpr(Spanned<TypeSign>, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeOrExpr {
    Type(Type),
    Expr(Expr),
}

impl HasSpan for TypeOrExpr {
    fn span(&self) -> Span {
        match *self {
            TypeOrExpr::Type(ref x) => x.span(),
            TypeOrExpr::Expr(ref x) => x.span(),
        }
    }

    fn human_span(&self) -> Span {
        match *self {
            TypeOrExpr::Type(ref x) => x.human_span(),
            TypeOrExpr::Expr(ref x) => x.human_span(),
        }
    }
}

impl HasDesc for TypeOrExpr {
    fn desc(&self) -> &'static str {
        match *self {
            TypeOrExpr::Type(ref x) => x.desc(),
            TypeOrExpr::Expr(ref x) => x.desc(),
        }
    }

    fn desc_full(&self) -> String {
        match *self {
            TypeOrExpr::Type(ref x) => x.desc_full(),
            TypeOrExpr::Expr(ref x) => x.desc_full(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueRange {
    Single(Expr),
    Range { lo: Expr, hi: Expr, span: Span },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RangeMode {
    Absolute,
    RelativeDown,
    RelativeUp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Identifier {
    pub span: Span,
    pub name: Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallArg {
    pub span: Span,
    pub name_span: Span,
    pub name: Option<Name>,
    pub expr: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StreamConcatSlice {
    Expr(Box<Expr>),
    Type(Type),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StreamExpr {
    pub expr: Box<Expr>,
    pub range: Option<Box<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventExpr {
    Edge {
        span: Span,
        edge: EdgeIdent,
        value: Expr,
    },
    Iff {
        span: Span,
        expr: Box<EventExpr>,
        cond: Expr,
    },
    Or {
        span: Span,
        lhs: Box<EventExpr>,
        rhs: Box<EventExpr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeIdent {
    Implicit,
    Edge,
    Posedge,
    Negedge,
}

impl HasSpan for EventExpr {
    fn span(&self) -> Span {
        match *self {
            EventExpr::Edge { span: sp, .. } => sp,
            EventExpr::Iff { span: sp, .. } => sp,
            EventExpr::Or { span: sp, .. } => sp,
        }
    }
}

impl HasDesc for EventExpr {
    fn desc(&self) -> &'static str {
        "event expression"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassDecl {
    pub span: Span,
    pub virt: bool,
    pub lifetime: Lifetime, // default static
    pub name: Identifier,
    pub params: Vec<ParamDecl>,
    pub extends: Option<(Type, Vec<CallArg>)>,
    pub impls: Vec<Identifier>,
    pub items: Vec<ClassItem>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassItem {
    pub span: Span,
    pub qualifiers: Vec<(ClassItemQualifier, Span)>,
    pub data: ClassItemData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassItemQualifier {
    Static,
    Protected,
    Local,
    Rand,
    Randc,
    Pure,
    Virtual,
    Const,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassItemData {
    Property,
    Typedef(Typedef),
    SubroutineDecl(SubroutineDecl),
    ExternSubroutine(SubroutinePrototype),
    Constraint(Constraint),
    ClassDecl,
    CovergroupDecl,
    ParamDecl(ParamDecl),
    Null,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RandomQualifier {
    Rand,
    Randc,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Typedef {
    pub span: Span,
    pub name: Identifier,
    pub ty: Type,
    pub dims: Vec<TypeDim>,
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
        format!("typedef `{}`", self.name.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    pub span: Span,
    pub kind: ConstraintKind,
    pub statik: bool,
    pub name: Name,
    pub name_span: Span,
    pub items: Vec<ConstraintItem>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    Decl,
    Proto,
    ExternProto,
    PureProto,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintItem {
    pub span: Span,
    pub data: ConstraintItemData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintItemData {
    If,
    Foreach,
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutineDecl {
    pub span: Span,
    pub prototype: SubroutinePrototype,
    pub items: Vec<SubroutineItem>,
}

impl HasSpan for SubroutineDecl {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.prototype.name.span
    }
}

impl HasDesc for SubroutineDecl {
    fn desc(&self) -> &'static str {
        match self.prototype.kind {
            SubroutineKind::Func => "function declaration",
            SubroutineKind::Task => "task declaration",
        }
    }

    fn desc_full(&self) -> String {
        match self.prototype.kind {
            SubroutineKind::Func => format!("function `{}`", self.prototype.name.name),
            SubroutineKind::Task => format!("task `{}`", self.prototype.name.name),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePrototype {
    pub span: Span,
    pub kind: SubroutineKind,
    pub lifetime: Option<Lifetime>,
    pub name: Identifier,
    pub args: Vec<SubroutinePort>,
    pub retty: Option<Type>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SubroutineKind {
    Func,
    Task,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePort {
    pub span: Span,
    pub dir: Option<SubroutinePortDir>,
    pub var: bool,
    pub ty: Type,
    pub name: Option<SubroutinePortName>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePortName {
    pub name: Identifier,
    pub dims: Vec<TypeDim>,
    pub expr: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubroutineItem {
    PortDecl(SubroutinePortDecl),
    Stmt(Stmt),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePortDecl {
    pub span: Span,
    pub dir: SubroutinePortDir,
    pub var: bool,
    pub ty: Type,
    pub names: Vec<VarDeclName>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubroutinePortDir {
    Input,
    Output,
    Inout,
    Ref,
    ConstRef,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NetDecl {
    pub span: Span,
    pub net_type: NetType,
    pub strength: Option<NetStrength>,
    pub kind: NetKind,
    pub ty: Type,
    pub delay: Option<DelayControl>,
    pub names: Vec<VarDeclName>,
}

impl HasSpan for NetDecl {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for NetDecl {
    fn desc(&self) -> &'static str {
        "net declaration"
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetKind {
    Vectored,
    Scalared,
    None,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetStrength {
    Drive(DriveStrength, DriveStrength),
    Charge(ChargeStrength),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DriveStrength {
    Supply0,
    Strong0,
    Pull0,
    Weak0,
    HighZ0,
    Supply1,
    Strong1,
    Pull1,
    Weak1,
    HighZ1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChargeStrength {
    Small,
    Medium,
    Large,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatternField {
    pub span: Span,
    pub data: PatternFieldData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternFieldData {
    Default(Box<Expr>),
    Member(Box<Expr>, Box<Expr>),
    Type(Type, Box<Expr>),
    Expr(Box<Expr>),
    Repeat(Box<Expr>, Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl {
    pub span: Span,
    pub items: Vec<ImportItem>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportItem {
    pub pkg: Identifier,
    pub name: Option<Identifier>, // None means `import pkg::*`
}

impl HasSpan for ImportItem {
    fn span(&self) -> Span {
        let mut sp = self.pkg.span;
        if let Some(name) = self.name {
            sp.expand(name.span);
        }
        sp
    }
}

impl HasDesc for ImportItem {
    fn desc(&self) -> &'static str {
        "import"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assertion {
    pub span: Span,
    pub label: Option<(Name, Span)>,
    pub data: AssertionData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionData {
    Immediate(BlockingAssertion),
    Deferred(AssertionDeferred, BlockingAssertion),
    Concurrent(ConcurrentAssertion),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionDeferred {
    /// `assert #0`
    Observed,
    /// `assert final`
    Final,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockingAssertion {
    Assert(Expr, AssertionActionBlock),
    Assume(Expr, AssertionActionBlock),
    Cover(Expr, Stmt),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcurrentAssertion {
    AssertProperty(PropSpec, AssertionActionBlock),
    AssumeProperty(PropSpec, AssertionActionBlock),
    CoverProperty(PropSpec, Stmt),
    CoverSequence,
    ExpectProperty(PropSpec, AssertionActionBlock),
    RestrictProperty(PropSpec),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionActionBlock {
    Positive(Stmt),
    Negative(Stmt),
    Both(Stmt, Stmt),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeqExpr {
    pub span: Span,
    pub data: SeqExprData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqExprData {
    Expr(Expr, Option<SeqRep>),
    BinOp(SeqBinOp, Box<SeqExpr>, Box<SeqExpr>),
    Throughout(Expr, Box<SeqExpr>),
    Clocked(EventExpr, Box<SeqExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqRep {
    Consec(Expr),    // [* expr]
    ConsecStar,      // [*]
    ConsecPlus,      // [+]
    Nonconsec(Expr), // [= expr]
    Goto(Expr),      // [-> expr]
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeqBinOp {
    Or,
    And,
    Intersect,
    Within,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropSpec;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropExpr {
    pub span: Span,
    pub data: PropExprData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropExprData {
    SeqOp(PropSeqOp, SeqExpr),
    SeqBinOp(PropSeqBinOp, PropSeqOp, SeqExpr, Box<PropExpr>),
    Not(Box<PropExpr>),
    BinOp(PropBinOp, Box<PropExpr>, Box<PropExpr>),
    Clocked(EventExpr, Box<PropExpr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropSeqOp {
    None,
    Weak,
    Strong,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropSeqBinOp {
    ImplOverlap,
    ImplNonoverlap,
    FollowOverlap,
    FollowNonoverlap,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropBinOp {
    Or,
    And,
    Until,
    SUntil,
    UntilWith,
    SUntilWith,
    Impl,
    Iff,
    SeqImplOl,
    SeqImplNol,
    SeqFollowOl,
    SeqFollowNol,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inst {
    pub span: Span,
    /// The name of the module to instantiate.
    pub target: Identifier,
    /// The parameters in the module to be assigned.
    pub params: Vec<ParamAssignment>,
    /// The names and ports of the module instantiations.
    pub names: Vec<InstName>,
}

impl HasSpan for Inst {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.target.span
    }
}

impl HasDesc for Inst {
    fn desc(&self) -> &'static str {
        "instantiation"
    }

    fn desc_full(&self) -> String {
        format!("`{}` instantiation", self.target.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstName {
    pub span: Span,
    pub name: Identifier,
    pub dims: Vec<TypeDim>,
    pub conns: Vec<PortConn>,
}

impl HasSpan for InstName {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for InstName {
    fn desc(&self) -> &'static str {
        "instance"
    }

    fn desc_full(&self) -> String {
        format!("instance `{}`", self.name.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModportDecl {
    pub span: Span,
    pub items: Vec<ModportItem>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModportItem {
    pub span: Span,
    pub name: Identifier,
    pub ports: Vec<ModportPort>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModportPort {
    Port,
}

/// A parameter or localparam declaration.
///
/// ```text
/// "localparam" data_type_or_implicit list_of_param_assignments
/// "localparam" "type" list_of_type_assignments
/// "parameter" data_type_or_implicit list_of_param_assignments
/// "parameter" "type" list_of_type_assignments
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamDecl {
    pub span: Span,
    pub local: bool,
    pub kind: ParamKind,
}

impl HasSpan for ParamDecl {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for ParamDecl {
    fn desc(&self) -> &'static str {
        "parameter"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamKind {
    Type(Vec<ParamTypeDecl>),
    Value(Vec<ParamValueDecl>),
}

/// A single type assignment within a parameter or localparam declaration.
///
/// ```text
/// ident ["=" type]
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamTypeDecl {
    pub span: Span,
    pub name: Identifier,
    pub ty: Option<Type>,
}

impl HasSpan for ParamTypeDecl {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for ParamTypeDecl {
    fn desc(&self) -> &'static str {
        "parameter"
    }

    fn desc_full(&self) -> String {
        format!("parameter `{}`", self.name.name)
    }
}

/// A single value assignment within a parameter or loclparam declaration.
///
/// ```text
/// [type_or_implicit] ident {dimension} ["=" expr]
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamValueDecl {
    pub span: Span,
    pub ty: Type,
    pub name: Identifier,
    pub dims: Vec<TypeDim>,
    pub expr: Option<Expr>,
}

impl HasSpan for ParamValueDecl {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for ParamValueDecl {
    fn desc(&self) -> &'static str {
        "parameter"
    }

    fn desc_full(&self) -> String {
        format!("parameter `{}`", self.name.name)
    }
}

/// A continuous assignment statement.
///
/// ```text
/// "assign" [drive_strength] [delay3] list_of_assignments ";"
/// "assign" [delay_control] list_of_assignments ";"
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContAssign {
    pub span: Span,
    pub strength: Option<(DriveStrength, DriveStrength)>,
    pub delay: Option<Expr>,
    pub delay_control: Option<DelayControl>,
    pub assignments: Vec<(Expr, Expr)>,
}

impl HasSpan for ContAssign {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for ContAssign {
    fn desc(&self) -> &'static str {
        "continuous assignment"
    }
}

#[derive(CommonNode, Debug, Clone, PartialEq, Eq)]
pub struct GenerateFor {
    #[ignore_child]
    pub span: Span,
    pub init: Stmt,
    pub cond: Expr,
    pub step: Expr,
    pub block: GenerateBlock,
}

impl HasSpan for GenerateFor {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for GenerateFor {
    fn desc(&self) -> &'static str {
        "for-generate statement"
    }
}

#[derive(CommonNode)]
pub struct TupleDummy(usize, usize, Expr);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateIf {
    pub span: Span,
    pub cond: Expr,
    pub main_block: GenerateBlock,
    pub else_block: Option<GenerateBlock>,
}

impl HasSpan for GenerateIf {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for GenerateIf {
    fn desc(&self) -> &'static str {
        "if-generate statement"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateCase {
    // TODO
}

impl HasSpan for GenerateCase {
    fn span(&self) -> Span {
        // TODO: Fix this once we have a proper case statement.
        INVALID_SPAN
    }
}

impl HasDesc for GenerateCase {
    fn desc(&self) -> &'static str {
        "case-generate statement"
    }
}

/// A body of a generate construct. May contains hierarchy items or more
/// generate constructs.
#[derive(CommonNode, Debug, Clone, PartialEq, Eq)]
pub struct GenerateBlock {
    pub span: Span,
    #[ignore_child]
    pub label: Option<Name>,
    #[ignore_child]
    pub items: Vec<Item>,
}

impl HasSpan for GenerateBlock {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for GenerateBlock {
    fn desc(&self) -> &'static str {
        "generate statement"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamAssignment {
    pub span: Span,
    pub name: Option<Identifier>,
    pub expr: TypeOrExpr,
}

/// A port connection as given in an instantiation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortConn {
    pub span: Span,
    pub kind: PortConnKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PortConnKind {
    Auto,                            // `.*` case
    Named(Identifier, PortConnMode), // `.name`, `.name()`, `.name(expr)` cases
    Positional(Expr),                // `expr` case
}

/// Represents how a named port connection is made.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PortConnMode {
    Auto,            // `.name` case
    Unconnected,     // `.name()` case
    Connected(Expr), // `.name(expr)` case
}
