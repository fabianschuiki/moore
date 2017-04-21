// Copyright (c) 2016-2017 Fabian Schuiki
use moore_common::source::Span;
use moore_common::name::Name;
use std::fmt;
use super::token::{Op, Lit};


/// A positive, small ID assigned to each node in the AST. Used as a lightweight
/// way to refer to individual nodes, e.g. during symbol table construction and
/// name resolution.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash, Debug, RustcEncodable, RustcDecodable)]
pub struct NodeId(u32);

impl NodeId {
    pub fn new(x: usize) -> NodeId {
		use std::u32;
        assert!(x < (u32::MAX as usize));
        NodeId(x as u32)
    }

    pub fn from_u32(x: u32) -> NodeId {
        NodeId(x)
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    pub fn as_u32(&self) -> u32 {
        self.0
    }
}

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

/// During parsing and syntax tree construction, we assign each node this ID.
/// Only later, during the renumbering pass do we assign actual IDs to each
/// node.
pub const DUMMY_NODE_ID: NodeId = NodeId(0);



pub use self::TypeData::*;
pub use self::StmtData::*;
pub use self::ExprData::*;


#[derive(Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Root {
	pub timeunits: Option<Timeunit>,
	pub items: Vec<Item>,
}


#[derive(Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum Item {
	Module(ModDecl),
	Interface(IntfDecl),
	Package(PackageDecl),
	Item(HierarchyItem),
	// Program(ProgramDecl),
	// Bind(BindDirective),
	// Config(ConfigDecl),
}

impl Item {
	pub fn span(&self) -> Span {
		match *self {
			Item::Module(ref decl) => decl.span,
			Item::Interface(ref decl) => decl.span,
			Item::Package(ref decl) => decl.span,
			Item::Item(ref item) => item.span(),
		}
	}

	pub fn as_str(&self) -> &'static str {
		match *self {
			Item::Module(ref decl) => "module declaration",
			Item::Interface(ref decl) => "interface declaration",
			Item::Package(ref decl) => "package declaration",
			Item::Item(ref item) => item.as_str(),
		}
	}
}


#[derive(Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ModDecl {
	pub id: NodeId,
	pub span: Span,
	pub lifetime: Lifetime, // default static
	pub name: Name,
	pub name_span: Span,
	pub params: Vec<ParamDecl>,
	pub ports: Vec<Port>,
	pub items: Vec<HierarchyItem>,
}

#[derive(Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct IntfDecl {
	pub id: NodeId,
	pub span: Span,
	pub lifetime: Lifetime, // default static
	pub name: Name,
	pub name_span: Span,
	pub ports: Vec<Port>,
	pub items: Vec<HierarchyItem>,
}

#[derive(Debug, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct PackageDecl {
	pub id: NodeId,
	pub span: Span,
	pub lifetime: Lifetime,
	pub name: Name,
	pub name_span: Span,
	pub timeunits: Timeunit,
	pub items: Vec<HierarchyItem>,
}



/// Lifetime specifier for variables, tasks, and functions. Defaults to static.
#[derive(Debug, PartialEq, Eq, Clone, RustcEncodable, RustcDecodable)]
pub enum Lifetime {
	Static,
	Automatic,
}

#[derive(Debug, PartialEq, Eq, Clone, RustcEncodable, RustcDecodable)]
pub struct Timeunit;



#[derive(Debug, PartialEq, Eq, Clone, RustcEncodable, RustcDecodable)]
pub enum HierarchyItem {
	Dummy,
	ImportDecl(ImportDecl),
	LocalparamDecl(()),
	ParameterDecl(()),
	ParamDecl(ParamDecl),
	ModportDecl(ModportDecl),
	ClassDecl(ClassDecl),
	Typedef(Typedef),
	PortDecl(PortDecl),
	Procedure(Procedure),
	SubroutineDecl(SubroutineDecl),
	ContAssign(ContAssign),
	GenvarDecl(Vec<GenvarDecl>),
	GenerateRegion(Span, Vec<HierarchyItem>),
	GenerateFor(GenerateFor),
	GenerateIf(GenerateIf),
	GenerateCase(GenerateCase),
	Assertion(Assertion),
	NetDecl(NetDecl),
	VarDecl(VarDecl),
	Inst(Inst),
}

impl HierarchyItem {
	pub fn span(&self) -> Span {
		match *self {
			HierarchyItem::ImportDecl(ref decl) => decl.span,
			HierarchyItem::ParamDecl(ref decl) => decl.span,
			HierarchyItem::ModportDecl(ref decl) => decl.span,
			HierarchyItem::ClassDecl(ref decl) => decl.span,
			HierarchyItem::PortDecl(ref decl) => decl.span,
			HierarchyItem::Procedure(ref prc) => prc.span,
			HierarchyItem::SubroutineDecl(ref decl) => decl.span,
			HierarchyItem::Assertion(ref assertion) => assertion.span,
			HierarchyItem::NetDecl(ref decl) => decl.span,
			HierarchyItem::VarDecl(ref decl) => decl.span,
			HierarchyItem::Inst(ref inst) => inst.span,
			_ => unimplemented!(), // TODO remove this and have the compiler complain
		}
	}

	pub fn as_str(&self) -> &'static str {
		match *self {
			HierarchyItem::ImportDecl(ref decl) => "import declaration",
			HierarchyItem::ParamDecl(ref decl) => "parameter declaration",
			HierarchyItem::ModportDecl(ref decl) => "modport declaration",
			HierarchyItem::ClassDecl(ref decl) => "class declaration",
			HierarchyItem::PortDecl(ref decl) => "port declaration",
			HierarchyItem::Procedure(ref prc) => "procedure declaration",
			HierarchyItem::SubroutineDecl(ref decl) => "subroutine declaration",
			HierarchyItem::Assertion(ref assertion) => "assertion",
			HierarchyItem::NetDecl(ref decl) => "net declaration",
			HierarchyItem::VarDecl(ref decl) => "variable declaration",
			HierarchyItem::Inst(ref inst) => "instantiation",
			_ => unimplemented!(), // TODO remove this and have the compiler complain
		}
	}
}



#[derive(Debug, PartialEq, Eq, Clone, RustcEncodable, RustcDecodable)]
pub struct Type {
	pub span: Span,
	pub data: TypeData,
	pub sign: TypeSign,
	pub dims: Vec<TypeDim>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum TypeData {
	ImplicitType,
	VoidType,
	NamedType(Identifier),
	StringType,
	ChandleType,
	VirtIntfType(Name),
	EventType,
	MailboxType,

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
	SpecializedType(Box<Type>, Vec<()>),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
pub enum TypeSign {
	None,
	Signed,
	Unsigned,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum TypeDim {
	Expr(Expr),
	Range(Expr,Expr),
	Queue,
	Unsized,
	Associative,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct EnumName {
	pub span: Span,
	pub name: Identifier,
	pub range: Option<Expr>,
	pub value: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
pub enum StructKind {
	Struct,
	Union,
	TaggedUnion,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct StructMember {
	pub span: Span,
	pub rand_qualifier: Option<RandomQualifier>,
	pub ty: Box<Type>,
	pub names: Vec<VarDeclName>,
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
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

impl Port {
	pub fn span(&self) -> Span {
		match *self {
			Port::Intf{ span, .. } => span,
			Port::Explicit{ span, .. } => span,
			Port::Named{ span, .. } => span,
			Port::Implicit(ref expr) => expr.span,
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct PortDecl {
	pub span: Span,
	pub dir: PortDir,
	pub net_type: Option<NetType>,
	pub var: bool,
	pub ty: Type,
	pub names: Vec<VarDeclName>,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
pub enum PortKind {
	Net(NetType),
	Var,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
pub enum PortDir {
	Input,
	Output,
	Inout,
	Ref,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ParamPort {
	pub span: Span,
	pub name: Identifier,
	pub dims: Vec<TypeDim>,
	pub expr: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
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



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Procedure {
	pub span: Span,
	pub kind: ProcedureKind,
	pub stmt: Stmt,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
pub enum ProcedureKind {
	Initial,
	Always,
	AlwaysComb,
	AlwaysLatch,
	AlwaysFf,
	Final,
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Stmt {
	pub span: Span,
	pub label: Option<Name>,
	pub data: StmtData,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum StmtData {
	NullStmt,
	SequentialBlock(Vec<Stmt>),
	ParallelBlock(Vec<Stmt>, JoinKind),
	IfStmt {
		up: Option<UniquePriority>,
		cond: Expr,
		main_stmt: Box<Stmt>,
		else_stmt: Option<Box<Stmt>>
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

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
pub enum JoinKind {
	All,
	Any,
	None,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
pub enum UniquePriority {
	Unique,
	Unique0,
	Priority,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
pub enum CaseKind {
	Normal,
	DontCareZ,
	DontCareXZ,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, RustcEncodable, RustcDecodable)]
pub enum CaseMode {
	Normal,
	Inside,
	Pattern,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum CaseItem {
	Default(Box<Stmt>),
	Expr(Vec<Expr>, Box<Stmt>),
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct DelayControl {
	pub span: Span,
	pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct EventControl {
	pub span: Span,
	pub data: EventControlData,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum EventControlData {
	Implicit,
	Expr(EventExpr),
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct CycleDelay {

}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum TimingControl {
	Delay(DelayControl),
	Event(EventControl),
	Cycle(CycleDelay),
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
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


#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct VarDecl {
	pub span: Span,
	pub konst: bool,
	pub var: bool,
	pub lifetime: Option<Lifetime>,
	pub ty: Type,
	pub names: Vec<VarDeclName>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct VarDeclName {
	pub id: NodeId,
	pub span: Span,
	pub name: Name,
	pub name_span: Span,
	pub dims: Vec<TypeDim>,
	pub init: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct GenvarDecl {
	pub id: NodeId,
	pub span: Span,
	pub name: Name,
	pub name_span: Span,
	pub init: Option<Expr>,
}



// TODO: Assign a id to each and every expression. This will later allow the
// types of each expression to be recorded properly, and simplifies the act of
// assigning IDs. Maybe expression IDs should be distinct from node IDs?
#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Expr {
	pub span: Span,
	pub data: ExprData,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ExprData {
	DummyExpr,
	LiteralExpr(Lit),
	IdentExpr(Identifier),
	SysIdentExpr(Identifier),
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum RangeMode {
	Absolute,
	RelativeDown,
	RelativeUp,
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Identifier {
	pub id: NodeId,
	pub span: Span,
	pub name: Name,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct CallArg {
	pub span: Span,
	pub name_span: Span,
	pub name: Option<Name>,
	pub expr: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum StreamConcatSlice {
	Expr(Box<Expr>),
	Type(Type),
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct StreamExpr {
	pub expr: Box<Expr>,
	pub range: Option<Box<Expr>>,
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum EventExpr {
	Edge {
		span:  Span,
		edge:  EdgeIdent,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum EdgeIdent {
	Implicit,
	Edge,
	Posedge,
	Negedge,
}

impl EventExpr {
	pub fn span(&self) -> Span {
		match *self {
			EventExpr::Edge { span: sp, .. } => sp,
			EventExpr::Iff { span: sp, .. } => sp,
			EventExpr::Or { span: sp, .. } => sp,
		}
	}
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ClassDecl {
	pub span: Span,
	pub virt: bool,
	pub lifetime: Lifetime, // default static
	pub name: Identifier,
	pub params: Vec<ParamDecl>,
	pub extends: Option<(Type, Vec<CallArg>)>,
	pub items: Vec<ClassItem>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ClassItem {
	pub span: Span,
	pub qualifiers: Vec<(ClassItemQualifier,Span)>,
	pub data: ClassItemData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
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

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ClassItemData {
	Property,
	SubroutineDecl(SubroutineDecl),
	ExternSubroutine(SubroutinePrototype),
	Constraint(Constraint),
	ClassDecl,
	CovergroupDecl,
	LocalparamDecl(()),
	ParameterDecl(()),
	Null,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum RandomQualifier {
	Rand,
	Randc,
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Typedef {
	pub span: Span,
	pub name: Identifier,
	pub ty: Type,
	pub dims: Vec<TypeDim>,
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Constraint {
	pub span: Span,
	pub kind: ConstraintKind,
	pub statik: bool,
	pub name: Name,
	pub name_span: Span,
	pub items: Vec<ConstraintItem>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ConstraintKind {
	Decl,
	Proto,
	ExternProto,
	PureProto,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ConstraintItem {
	pub span: Span,
	pub data: ConstraintItemData,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ConstraintItemData {
	If,
	Foreach,
	Expr(Expr),
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SubroutineDecl {
	pub span: Span,
	pub prototype: SubroutinePrototype,
	pub items: Vec<SubroutineItem>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SubroutinePrototype {
	pub span: Span,
	pub kind: SubroutineKind,
	pub name: Identifier,
	pub args: Vec<SubroutinePort>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SubroutineKind {
	Func,
	Task,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SubroutinePort {
	pub span: Span,
	pub dir: Option<SubroutinePortDir>,
	pub var: bool,
	pub ty: Type,
	pub name: Option<SubroutinePortName>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SubroutinePortName {
	pub name: Identifier,
	pub dims: Vec<TypeDim>,
	pub expr: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SubroutineItem {
	PortDecl(SubroutinePortDecl),
	Stmt(Stmt),
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SubroutinePortDecl {
	pub span: Span,
	pub dir: SubroutinePortDir,
	pub var: bool,
	pub ty: Type,
	pub names: Vec<VarDeclName>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SubroutinePortDir {
	Input,
	Output,
	Inout,
	Ref,
	ConstRef,
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct NetDecl {
	pub span: Span,
	pub net_type: NetType,
	pub strength: Option<NetStrength>,
	pub kind: NetKind,
	pub ty: Type,
	pub delay: Option<Expr>,
	pub names: Vec<VarDeclName>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum NetKind {
	Vectored,
	Scalared,
	None,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum NetStrength {
	Drive(DriveStrength, DriveStrength),
	Charge(ChargeStrength),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ChargeStrength {
	Small,
	Medium,
	Large,
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct PatternField {
	pub span: Span,
	pub data: PatternFieldData,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum PatternFieldData {
	Default(Box<Expr>),
	Member(Box<Expr>, Box<Expr>),
	Type(Type, Box<Expr>),
	Expr(Box<Expr>),
	Repeat(Box<Expr>, Vec<Expr>),
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ImportDecl {
	pub span: Span,
	pub items: Vec<ImportItem>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ImportItem {
	pub pkg: Identifier,
	pub name: Option<Identifier>, // None means `import pkg::*`
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Assertion {
	pub span: Span,
	pub label: Option<(Name, Span)>,
	pub data: AssertionData,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum AssertionData {
	Immediate(BlockingAssertion),
	Deferred(BlockingAssertion),
	Concurrent(ConcurrentAssertion),
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum BlockingAssertion {
	Assert(Expr, AssertionActionBlock),
	Assume(Expr, AssertionActionBlock),
	Cover(Expr, Stmt),
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ConcurrentAssertion {
	AssertProperty(PropSpec, AssertionActionBlock),
	AssumeProperty(PropSpec, AssertionActionBlock),
	CoverProperty(PropSpec, Stmt),
	CoverSequence,
	ExpectProperty(PropSpec, AssertionActionBlock),
	RestrictProperty(PropSpec),
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum AssertionActionBlock {
	Positive(Stmt),
	Negative(Stmt),
	Both(Stmt, Stmt),
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct SeqExpr {
	pub span: Span,
	pub data: SeqExprData,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SeqExprData {
	Expr(Expr, Option<SeqRep>),
	BinOp(SeqBinOp, Box<SeqExpr>, Box<SeqExpr>),
	Throughout(Expr, Box<SeqExpr>),
	Clocked(EventExpr, Box<SeqExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SeqRep {
	Consec(Expr),    // [* expr]
	ConsecStar,      // [*]
	ConsecPlus,      // [+]
	Nonconsec(Expr), // [= expr]
	Goto(Expr),      // [-> expr]
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum SeqBinOp {
	Or,
	And,
	Intersect,
	Within,
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct PropSpec;

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct PropExpr {
	pub span: Span,
	pub data: PropExprData,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum PropExprData {
	SeqOp(PropSeqOp, SeqExpr),
	SeqBinOp(PropSeqBinOp, PropSeqOp, SeqExpr, Box<PropExpr>),
	Not(Box<PropExpr>),
	BinOp(PropBinOp, Box<PropExpr>, Box<PropExpr>),
	Clocked(EventExpr, Box<PropExpr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum PropSeqOp {
	None,
	Weak,
	Strong,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum PropSeqBinOp {
	ImplOverlap,
	ImplNonoverlap,
	FollowOverlap,
	FollowNonoverlap,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable)]
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



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct Inst {
	pub span: Span,
	pub params: Vec<()>,
	pub names: Vec<InstName>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct InstName {
	pub span: Span,
	pub name: Identifier,
	pub dims: Vec<TypeDim>,
	pub conns: Vec<()>,
}



#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ModportDecl {
	pub span: Span,
	pub items: Vec<ModportItem>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ModportItem {
	pub span: Span,
	pub name: Identifier,
	pub ports: Vec<ModportPort>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
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
#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ParamDecl {
	pub span: Span,
	pub local: bool,
	pub kind: ParamKind,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub enum ParamKind {
	Type(Vec<ParamTypeDecl>),
	Value(Vec<ParamValueDecl>),
}

/// A single type assignment within a parameter or localparam declaration.
///
/// ```text
/// ident ["=" type]
/// ```
#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ParamTypeDecl {
	pub span: Span,
	pub name: Identifier,
	pub ty: Option<Type>,
}

/// A single value assignment within a parameter or loclparam declaration.
///
/// ```text
/// [type_or_implicit] ident {dimension} ["=" expr]
/// ```
#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ParamValueDecl {
	pub span: Span,
	pub ty: Type,
	pub name: Identifier,
	pub dims: Vec<TypeDim>,
	pub expr: Option<Expr>,
}



/// A continuous assignment statement.
///
/// ```text
/// "assign" [drive_strength] [delay3] list_of_assignments ";"
/// "assign" [delay_control] list_of_assignments ";"
/// ```
#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct ContAssign {
	pub span: Span,
	pub strength: Option<(DriveStrength, DriveStrength)>,
	pub delay: Option<Expr>,
	pub delay_control: Option<DelayControl>,
	pub assignments: Vec<(Expr, Expr)>,
}


#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct GenerateFor {
	pub span: Span,
	pub init: Stmt,
	pub cond: Expr,
	pub step: Expr,
	pub block: GenerateBlock,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct GenerateIf {
	pub span: Span,
	pub cond: Expr,
	pub main_block: GenerateBlock,
	pub else_block: Option<GenerateBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct GenerateCase {
	// TODO
}

/// A body of a generate construct. May contains hierarchy items or more
/// generate constructs.
#[derive(Debug, Clone, PartialEq, Eq, RustcEncodable, RustcDecodable)]
pub struct GenerateBlock {
	pub span: Span,
	pub label: Option<Name>,
	pub items: Vec<HierarchyItem>,
}
