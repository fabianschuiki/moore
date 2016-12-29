// Copyright (c) 2016 Fabian Schuiki

use source::Span;
use name::Name;

pub use self::TypeData::*;
pub use self::PortKind::*;
pub use self::StmtData::*;
pub use self::ExprData::*;


#[derive(Debug)]
pub struct ModDecl {
	pub span: Span,
	pub lifetime: Lifetime, // default static
	pub name: Name,
	pub name_span: Span,
	pub ports: Vec<Port>,
}

#[derive(Debug)]
pub struct IntfDecl {
	pub span: Span,
	pub lifetime: Lifetime, // default static
	pub name: Name,
	pub name_span: Span,
	pub ports: Vec<Port>,
}



/// Lifetime specifier for variables, tasks, and functions. Defaults to static.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lifetime {
	Static,
	Automatic,
}



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
	pub span: Span,
	pub data: TypeData,
	pub sign: TypeSign,
	pub dims: Vec<TypeDim>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeData {
	ImplicitType,
	NamedType(Name),

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

	// Enumerations
	EnumType(Option<Box<Type>>, Vec<EnumName>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeSign {
	None,
	Signed,
	Unsigned,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDim {
	Expr,
	Range,
	Queue,
	Unsized,
	Associative,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumName {
	pub span: Span,
	pub name: Name,
	pub name_span: Span,
	pub range: Option<Expr>,
	pub value: Option<Expr>,
}



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Port {
	pub span: Span,
	pub name: Name,
	pub name_span: Span,
	// If kind, type, direction all omitted, inherit from previous port.
	pub kind: PortKind, // input,inout => net, output w. impl. type => net, output w. expl. type => var, ref => var
	pub ty: Type, // default logic
	pub dir: PortDir, // inherit or default inout if first
	pub dims: Vec<TypeDim>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PortKind {
	NetPort,
	VarPort,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PortDir {
	Input,
	Output,
	Inout,
	Ref,
}



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamPort {
	pub span: Span,
	pub name: Name,
	pub name_span: Span,
	pub ty: Type,
	pub dims: Vec<TypeDim>,
	pub init: (),
}



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Procedure {
	pub span: Span,
	pub kind: ProcedureKind,
	pub stmt: Stmt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcedureKind {
	Initial,
	Always,
	AlwaysComb,
	AlwaysLatch,
	AlwaysFf,
	Final,
}



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stmt {
	pub span: Span,
	pub label: Option<Name>,
	pub data: StmtData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
	ForeachStmt(Expr, Box<Stmt>),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JoinKind {
	All,
	Any,
	None,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UniquePriority {
	Unique,
	Unique0,
	Priority,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaseKind {
	Normal,
	DontCareZ,
	DontCareXZ,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
pub struct CycleDelay {

}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimingControl {
	Delay(DelayControl),
	Event(EventControl),
	Cycle(CycleDelay),
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
pub struct Expr {
	pub span: Span,
	pub data: ExprData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprData {
	DummyExpr,
	CallExpr(Box<Expr>, Vec<CallArg>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallArg {
	pub span: Span,
	pub name_span: Span,
	pub name: Option<Name>,
	pub expr: Option<Expr>,
}



#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
