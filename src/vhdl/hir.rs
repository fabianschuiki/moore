// Copyright (c) 2017 Fabian Schuiki

//! The High-level Intermediate Representation of a VHDL design.

use moore_common::source::*;
use moore_common::name::*;
use moore_common::util::HasSpan;
use score::*;
use typed_arena::Arena;
use syntax::ast;
use konst::*;
pub use syntax::ast::Dir;

/// A collection of arenas where HIR nodes may be allocated.
make_arenas!(
	pub struct Arenas {
		lib:                 Lib,
		entity:              Entity,
		arch:                Arch,
		intf_sig:            IntfSignal,
		subtype_ind:         SubtypeInd,
		package:             Package,
		package_body:        PackageBody,
		package_inst:        PackageInst,
		type_decl:           TypeDecl,
		subtype_decl:        SubtypeDecl,
		expr:                Expr,
		aggregate:           Aggregate,
		const_decl:          Decl<ConstDecl>,
		signal_decl:         Decl<SignalDecl>,
		variable_decl:       Decl<VarDecl>,
		file_decl:           Decl<FileDecl>,
		process_stmt:        ProcessStmt,
		sig_assign_stmt:     SigAssignStmt,
		array_type_index:    Spanned<ArrayTypeIndex>,
		subprog:             Subprog,
		subprog_body:        SubprogBody,
		subprog_inst:        SubprogInst,
		type_mark:           TypeMarkRef,
		wait_stmt:           Stmt<WaitStmt>,
		assert_stmt:         Stmt<AssertStmt>,
		report_stmt:         Stmt<ReportStmt>,
		// sig_assign_stmt:     Stmt<SigAssignStmt>,
		var_assign_stmt:     Stmt<VarAssignStmt>,
		call_stmt:           Stmt<CallStmt>,
		if_stmt:             Stmt<IfStmt>,
		case_stmt:           Stmt<CaseStmt>,
		loop_stmt:           Stmt<LoopStmt>,
		nexit_stmt:          Stmt<NexitStmt>,
		return_stmt:         Stmt<ReturnStmt>,
		null_stmt:           Stmt<NullStmt>,
	}
);

impl Arenas {
	/// Create a new set of arenas.
	pub fn new() -> Arenas {
		Default::default()
	}
}


#[derive(Debug)]
pub struct Lib {
	pub entities: Vec<EntityRef>,
	pub cfgs: Vec<CfgRef>,
	pub pkg_decls: Vec<PkgDeclRef>,
	pub pkg_insts: Vec<PkgInstRef>,
	pub ctxs: Vec<CtxRef>,
	pub archs: Vec<ArchRef>,
	pub pkg_bodies: Vec<PkgBodyRef>,
}

impl Lib {
	pub fn new() -> Lib {
		Lib {
			entities: Vec::new(),
			cfgs: Vec::new(),
			pkg_decls: Vec::new(),
			pkg_insts: Vec::new(),
			ctxs: Vec::new(),
			archs: Vec::new(),
			pkg_bodies: Vec::new(),
		}
	}
}


#[derive(Debug)]
pub struct Entity {
	/// The context items associated with the entity.
	pub ctx_items: CtxItemsRef,
	/// The library in which the entity is defined.
	pub lib: LibRef,
	/// The entity name.
	pub name: Spanned<Name>,
	/// The list of generics that the entity declares.
	pub generics: Vec<GenericRef>,
	/// The list of ports that the entity declares.
	pub ports: Vec<IntfSignalRef>,
}


#[derive(Debug)]
pub struct Arch {
	/// The context items associated with the entity.
	pub ctx_items: CtxItemsRef,
	/// The entity of the architecture.
	pub entity: EntityRef,
	/// The architecture name.
	pub name: Spanned<Name>,
	/// The list of declarations in the architecture.
	pub decls: Vec<DeclInBlockRef>,
	/// The list of statements in the architecture.
	pub stmts: Vec<ConcStmtRef>,
}


#[derive(Debug)]
pub struct IntfSignal {
	/// The name of this signal.
	pub name: Spanned<Name>,
	/// The mode of this signal.
	pub mode: IntfSignalMode,
	/// The type of this signal.
	pub ty: SubtypeIndRef,
	/// Whether this signal was declared with the `bus` keyword.
	pub bus: bool,
	/// The expression determining the initial value of this signals.
	pub init: Option<ExprRef>,
}


#[derive(Debug, Clone, Copy)]
pub enum IntfSignalMode {
	In,
	Out,
	Inout,
	Buffer,
	Linkage,
}


#[derive(Debug)]
pub struct SubtypeInd {
	/// The location within the source code.
	pub span: Span,
	/// The type mark.
	pub type_mark: Spanned<TypeMarkRef>,
	/// The optional constraint.
	pub constraint: Option<Spanned<Constraint>>,
}


/// A constraint.
///
/// See IEEE 1076-2008 section 6.3.
///
/// ```ignore
/// constraint := range_constraint | array_constraint | record_constraint
/// ```
#[derive(Debug)]
pub enum Constraint {
	/// A range constraint.
	Range(Range),
	/// An array constraint.
	Array(ArrayConstraint),
	/// A record constraint.
	Record(RecordConstraint),
}

impl From<ArrayConstraint> for Constraint {
	fn from(value: ArrayConstraint) -> Constraint {
		Constraint::Array(value)
	}
}

impl From<RecordConstraint> for Constraint {
	fn from(value: RecordConstraint) -> Constraint {
		Constraint::Record(value)
	}
}

/// An element constraint.
///
/// See IEEE 1076-2008 section 6.3.
///
/// ```ignore
/// element_constraint := array_constraint | record_constraint
/// ```
#[derive(Debug)]
pub enum ElementConstraint {
	Array(ArrayConstraint),
	Record(RecordConstraint),
}

impl HasSpan for ElementConstraint {
	fn span(&self) -> Span {
		match *self {
			ElementConstraint::Array(ref n) => n.span(),
			ElementConstraint::Record(ref n) => n.span(),
		}
	}
}

impl From<ArrayConstraint> for ElementConstraint {
	fn from(value: ArrayConstraint) -> ElementConstraint {
		ElementConstraint::Array(value)
	}
}

impl From<RecordConstraint> for ElementConstraint {
	fn from(value: RecordConstraint) -> ElementConstraint {
		ElementConstraint::Record(value)
	}
}

/// An array constraint.
///
/// See IEEE 1076-2008 section 5.3.2.
///
/// ```ignore
/// array_constraint :=
///     index_constraint [array.element_constraint] |
///     "(" "open" ")" [array.element_constraint]
/// ```
#[derive(Debug)]
pub struct ArrayConstraint {
	/// The span this constraint covers.
	pub span: Span,
	/// The index constraint. An empty vector corresponds to the `open`
	/// constraint.
	pub index: Vec<Spanned<DiscreteRange>>,
	/// The optional element constraint.
	pub elem: Option<Box<Spanned<ElementConstraint>>>,
}

impl HasSpan for ArrayConstraint {
	fn span(&self) -> Span {
		self.span
	}
}

/// A discrete range.
///
/// See IEEE 1076-2008 section 5.3.2.1.
///
/// ```ignore
/// discrete_range := discrete.subtype_indication | range
/// ```
#[derive(Debug)]
pub enum DiscreteRange {
	/// A discrete range specified by a discrete subtype.
	Subtype(SubtypeIndRef),
	/// A discrete range specified by a range.
	Range(Range),
}

impl From<SubtypeIndRef> for DiscreteRange {
	fn from(value: SubtypeIndRef) -> DiscreteRange {
		DiscreteRange::Subtype(value)
	}
}

impl From<Range> for DiscreteRange {
	fn from(value: Range) -> DiscreteRange {
		DiscreteRange::Range(value)
	}
}

/// A range.
///
/// See IEEE 1076-2008 section 5.2.1.
///
/// ```ignore
/// range := range.attribute_name | simple_expression direction simple_expression
/// ```
#[derive(Debug)]
pub enum Range {
	// Attr(AttrRef),
	Immediate(Dir, ExprRef, ExprRef),
}


/// A record constraint as per IEEE 1076-2008 section 5.3.3.
#[derive(Debug)]
pub struct RecordConstraint {
	/// The span this constraint covers.
	pub span: Span,
	/// Constraints for individual elements.
	pub elems: Vec<(Spanned<Name>, Box<Spanned<ElementConstraint>>)>,
}

impl HasSpan for RecordConstraint {
	fn span(&self) -> Span {
		self.span
	}
}


/// A package declaration.
///
/// See IEEE 1076-2008 section 4.7.
#[derive(Debug)]
pub struct Package {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The package name.
	pub name: Spanned<Name>,
	/// The list of generics.
	pub generics: Vec<GenericRef>,
	/// The list of declarations in the package.
	pub decls: Vec<DeclInPkgRef>,
}

/// A package body.
///
/// See IEEE 1076-2008 section 4.8.
#[derive(Debug)]
pub struct PackageBody {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The package name.
	pub name: Spanned<Name>,
	/// The package which this body targets.
	pub pkg: Spanned<LatentPkgRef>,
	/// The declarations.
	pub decls: Vec<DeclInPkgBodyRef>,
}

/// A package instantiation.
///
/// See IEEE 1076-2008 section 4.9.
#[derive(Debug)]
pub struct PackageInst {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The name of the package.
	pub name: Spanned<Name>,
	/// The package to be instantiated.
	pub pkg: Spanned<LatentPkgRef>,
	/// The generic map.
	pub generic_map: Vec<()>,
}


#[derive(Debug)]
pub struct TypeDecl {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The type name.
	pub name: Spanned<Name>,
	/// The type data.
	pub data: Option<Spanned<TypeData>>,
}

/// The meat of a type declaration.
#[derive(Debug)]
pub enum TypeData {
	/// An enumeration type.
	Enum(Vec<EnumLit>),
	/// An integer, float, or physical type with optional units.
	Range(Dir, ExprRef, ExprRef),
	/// An access type.
	Access(SubtypeIndRef),
	/// An array type.
	Array(Vec<ArrayTypeIndexRef>, SubtypeIndRef),
	/// A file type.
	File(TypeMarkRef),
	/// A record type.
	Record(Vec<(Spanned<Name>, SubtypeIndRef)>),
}

/// An enumeration literal as listed in a type declaration.
#[derive(Debug)]
pub enum EnumLit {
	Ident(Spanned<Name>),
	Char(Spanned<char>),
}

/// An index of an array type.
#[derive(Debug)]
pub enum ArrayTypeIndex {
	/// An unbounded array index of the form `... range <>`.
	Unbounded(Spanned<TypeMarkRef>),
	/// A constrained array index of the form of a subtype indication.
	Subtype(SubtypeIndRef),
	/// A constrained array index of the form `... to/downto ...`.
	Range(Dir, ExprRef, ExprRef),
}


/// A subtype declaration as per IEEE 1076-2008 section 6.3.
#[derive(Debug)]
pub struct SubtypeDecl {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The subtype name.
	pub name: Spanned<Name>,
	/// The actualy subtype.
	pub subty: SubtypeIndRef,
}


/// An expression.
///
/// See IEEE 1076-2008 section 9.
#[derive(Debug)]
pub struct Expr {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The range in the source file that this expression covers.
	pub span: Span,
	/// The expression data.
	pub data: ExprData,
}

/// An expression variant.
#[derive(Debug)]
pub enum ExprData {
	/// A resolved name. Consists of the definition and the definition's span.
	Name(Def, Span),
	/// A resolved constant name.
	ConstName(ConstDeclRef),
	/// A resolved signal name.
	SignalName(SignalRef),
	/// A resolved variable name.
	VarName(VarDeclRef),
	/// A resolved file name.
	FileName(FileDeclRef),
	/// An overloaded resolved name.
	OverloadedName(Vec<Spanned<Def>>),
	/// A selection, e.g. `a.b`.
	Select(ExprRef, Spanned<ResolvableName>),
	/// An attribute selection, e.g. `a'b`.
	Attr(ExprRef, Spanned<ResolvableName>),
	/// A bit string literal.
	StringLiteral(Name),
	/// An integer literal.
	IntegerLiteral(ConstInt),
	/// A float literal.
	FloatLiteral(ConstFloat),
	/// A unary operator expression.
	Unary(Spanned<UnaryOp>, ExprRef),
	/// A binary operator expression.
	Binary(Operator, ExprRef, ExprRef),
	/// A range expression.
	Range(Dir, ExprRef, ExprRef),
	/// An aggregate expression.
	Aggregate(AggregateRef),
	/// A qualified expression.
	Qualified(Spanned<TypeMarkRef>, ExprRef),
	/// An allocator expression, i.e. `new`.
	Allocator(Spanned<TypeMarkRef>, Option<ExprRef>),
	/// A cast expression.
	Cast(Spanned<TypeMarkRef>, ExprRef),
	/// A function call expression.
	Call(ExprRef, Spanned<AssocList>),
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
	Logical(ast::LogicalOp),
}

/// A binary operator.
///
/// See IEEE 1076-2008 section 9.2.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BinaryOp {
	/// A logical operator.
	Logical(ast::LogicalOp),
	/// A relational operator.
	Rel(ast::RelationalOp),
	/// A matching relational operator. These are the relational operators
	/// prefixed with a `?`.
	Match(ast::RelationalOp),
	/// A shift operator.
	Shift(ast::ShiftOp),
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

/// An object declaration.
///
/// See IEEE 1076-2008 section 6.4.2.1/
#[derive(Debug)]
pub struct Decl<T> {
	/// The scope within which the declaration is made.
	pub parent: ScopeRef,
	/// The span this declaration covers.
	pub span: Span,
	/// The name of the declared object.
	pub name: Spanned<Name>,
	/// The actual declaration.
	pub decl: T,
}

/// A constant declaration.
///
/// See IEEE 1076-2008 section 6.4.2.2.
#[derive(Debug)]
pub struct ConstDecl {
	/// The type of the constant.
	pub ty: SubtypeIndRef,
	/// The optional initial value for the constant.
	pub init: Option<ExprRef>,
}

/// A signal declaration.
///
/// See IEEE 1076-2008 section 6.4.2.3.
#[derive(Debug)]
pub struct SignalDecl {
	/// The subtype of the signal.
	pub ty: SubtypeIndRef,
	/// The signal kind.
	pub kind: SignalKind,
	/// The optional initial value for the signals.
	pub init: Option<ExprRef>,
}

/// A signal kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignalKind {
	Normal,
	Register,
	Bus,
}

/// A variable declaration.
///
/// See IEEE 1076-2008 section 6.4.2.4.
#[derive(Debug)]
pub struct VarDecl {
	/// Whether the variable was declared as shared or not.
	pub shared: bool,
	/// The subtype of the variable.
	pub ty: SubtypeIndRef,
	/// The optional initial value for the variable.
	pub init: Option<ExprRef>,
}

/// A file declaration.
///
/// See IEEE 1076-2008 section 6.4.2.5.
#[derive(Debug)]
pub struct FileDecl {
	/// The subtype of the file.
	pub ty: SubtypeIndRef,
	/// The expression evaluating to the file name.
	pub filename: Option<ExprRef>,
	/// The expression evaluating to the opening mode.
	pub mode: Option<ExprRef>,
}

/// A process statement.
///
/// See IEEE 1076-2008 section 11.3.
#[derive(Debug)]
pub struct ProcessStmt {
	/// The scope within which the process is declared.
	pub parent: ScopeRef,
	/// The optional process label.
	pub label: Option<Spanned<Name>>,
	/// Whether this is a postponed process. See language reference.
	pub postponed: bool,
	/// The sensitivity list.
	pub sensitivity: ProcessSensitivity,
	/// The declarations made before the `begin` keyword.
	pub decls: Vec<DeclInProcRef>,
	/// The statements inside the process.
	pub stmts: Vec<SeqStmtRef>,
}

/// A process sensitivity specification.
///
/// See IEEE 1076-2008 section 11.3.
#[derive(Debug)]
pub enum ProcessSensitivity {
	/// No sensitivity list provided.
	None,
	/// The `all` sensitivity list.
	All,
	/// Explicitly enumerated signals.
	List(Vec<Def>),
}

/// A sequential signal assignment.
///
/// See IEEE 1076-2008 section 10.5.
#[derive(Debug)]
pub struct SigAssignStmt {
	/// The scope within which the statement has been made.
	pub parent: ScopeRef,
	/// The location of the entire statement in the source file.
	pub span: Span,
	/// The optional statement label.
	pub label: Option<Spanned<Name>>,
	/// The target of the assignment.
	pub target: SigAssignTarget,
	/// The location of the right hand side in the source file.
	pub target_span: Span,
	/// The kind of the assignment.
	pub kind: SigAssignKind,
	/// The location of the right hand side in the source file.
	pub kind_span: Span,
}

/// A signal assignment target.
#[derive(Debug)]
pub enum SigAssignTarget {
	Name(SignalRef),
	Aggregate,
}

/// A signal assignment kind.
#[derive(Debug)]
pub enum SigAssignKind {
	/// A simple waveform assignment.
	SimpleWave(DelayMechanism, Waveform),
	/// A simple force assignment.
	SimpleForce(ForceMode, ExprRef),
	/// A simple release assignment.
	SimpleRelease(ForceMode),
	/// A conditional waveform assignment.
	CondWave(DelayMechanism, Cond<Waveform>),
	/// A conditional force assignment.
	CondForce(ForceMode, Cond<ExprRef>),
	/// A selected waveform assignment.
	SelWave(DelayMechanism, Sel<Waveform>),
	/// A selected force assignment.
	SelForce(ForceMode, Sel<ExprRef>),
}

/// A conditional waveform or expression.
///
/// See IEEE 1076-2008 section 10.5.3.
#[derive(Debug)]
pub struct Cond<T> {
	/// The conditional values, represented as (value, cond) tuples.
	pub when: Vec<(T, ExprRef)>,
	/// The optional `else` value.
	pub other: Option<T>,
}

/// A selected waveform or expression.
///
/// See IEEE 1076-2008 section 10.5.4.
#[derive(Debug)]
pub struct Sel<T> {
	/// Whether matching comparisons are to be used.
	pub matching: bool,
	/// The discriminant expression that is used to select among the choices.
	pub disc: ExprRef,
	/// The selected values, represented as (value, choices) tuples.
	pub when: Vec<(T, Spanned<Choices>)>,
}

/// The mode of a signal force/release statement.
///
/// See IEEE 1076-2008 section 10.5.2.1.
#[derive(Copy, Clone, Debug)]
pub enum ForceMode {
	/// Specifies an effective-value force/release. This is the default if the
	/// assignment target is a in port/signal, or no port/signal at all.
	In,
	/// Specifies a driving-value force/release. This is the default if the
	/// assignment target is a out/inout/buffer port/signal.
	Out,
}

/// The delay mechanism of a normal signal assignment.
#[derive(Copy, Clone, Debug)]
pub enum DelayMechanism {
	/// A `transport` delay mechanism.
	Transport,
	/// A `inertial` delay mechanism.
	Inertial,
	/// A `reject <time_expr> inertial` delay mechanism.
	RejectInertial(ExprRef),
}

/// A signal assignment waveform.
///
/// An empty vector corresponds to the `unaffected` waveform.
pub type Waveform = Vec<WaveElem>;

/// An element of a signal assignment waveform.
#[derive(Debug)]
pub struct WaveElem {
	/// The value expression of the element. Corresponds to `null` if `None`.
	pub value: Option<ExprRef>,
	/// The optional `after` time expression.
	pub after: Option<ExprRef>,
}

/// A subprogram.
///
/// See IEEE 1076-2008 section 4.2.
#[derive(Clone, Debug)]
pub struct Subprog {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The specification, aka the signature.
	pub spec: SubprogSpec,
}

/// A subprogram body.
///
/// See IEEE 1076-2008 section 4.3.
#[derive(Clone, Debug)]
pub struct SubprogBody {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The specification, aka the signature.
	pub spec: SubprogSpec,
	/// The subprogram this body targets.
	pub subprog: Spanned<LatentSubprogRef>,
	/// The declarations in the subprogram.
	pub decls: Vec<DeclInSubprogRef>,
	/// The statements in the subprogram.
	pub stmts: Vec<SeqStmtRef>,
}

/// A subprogram instantiation.
///
/// See IEEE 1076-2008 section 4.4.
#[derive(Clone, Debug)]
pub struct SubprogInst {
	/// The parent scope.
	pub parent: ScopeRef,
	/// Whether this is a procedure, pure function, or impure function.
	pub kind: SubprogKind,
	/// The name of the subprogram.
	pub name: Spanned<ResolvableName>,
	/// The subprogram to be instantiated.
	pub subprog: Spanned<LatentSubprogRef>,
	/// The generic map.
	pub generic_map: Vec<()>,
}

/// A subprogram specification.
///
/// This can be thought of as the signature of a subprogram. It is shared by the
/// subprogram declaration and body, and must match.
#[derive(Clone, Debug)]
pub struct SubprogSpec {
	/// The name of the subprogram. For procedures this must be an identifier.
	pub name: Spanned<ResolvableName>,
	/// Whether this is a procedure, pure function, or impure function.
	pub kind: SubprogKind,
	/// The list of generics.
	pub generics: Vec<GenericRef>,
	/// The generic map.
	pub generic_map: Vec<()>,
	/// The subprogram parameters.
	pub params: Vec<IntfObjRef>,
	/// The return type.
	pub return_type: Option<Spanned<LatentTypeMarkRef>>,
}

/// A subprogram kind.
///
/// Identifies a subprogram as procedure, pure function, or impure function.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum SubprogKind {
	/// A procedure.
	Proc,
	/// A pure function.
	PureFunc,
	/// An impure function.
	ImpureFunc,
}

/// A statement.
///
/// See IEEE 1076-2008 section 10.1.
#[derive(Debug)]
pub struct Stmt<T> {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The span this statement covers.
	pub span: Span,
	/// The optional label.
	pub label: Option<Spanned<Name>>,
	/// The inner statement.
	pub stmt: T,
}

/// A wait statement.
///
/// See IEEE 1076-2008 section 10.2.
#[derive(Debug)]
pub struct WaitStmt {
	/// The sensitivity clause.
	pub sens: Option<Spanned<SensitivityList>>,
	/// The condition clause.
	pub cond: Option<ExprRef>,
	/// The timeout clause.
	pub timeout: Option<ExprRef>,
}

/// An assertion statement.
///
/// See IEEE 1076-2008 section 10.3.
#[derive(Debug)]
pub struct AssertStmt {
	/// The condition to be asserted.
	pub cond: ExprRef,
	/// The report message.
	pub report: Option<ExprRef>,
	/// The severity level.
	pub severity: Option<ExprRef>,
}

/// A report statement.
///
/// See IEEE 1076-2008 section 10.4.
#[derive(Debug)]
pub struct ReportStmt {
	/// The report message.
	pub report: ExprRef,
	/// The severity level.
	pub severity: Option<ExprRef>,
}

// pub struct SigAssignStmt;

/// A variable assignment statement.
///
/// See IEEE 1076-2008 section 10.6.
#[derive(Debug)]
pub struct VarAssignStmt {
	/// The target variable.
	pub target: Spanned<Target>,
	/// The assignment kind.
	pub kind: VarAssignKind,
}

/// A variable assignment kind.
#[derive(Debug)]
pub enum VarAssignKind {
	/// A simple assignment.
	Simple(ExprRef),
	/// A conditional assignment.
	Cond(Cond<ExprRef>),
	/// A selected assignment.
	Sel(Sel<ExprRef>),
}

/// A procedure call statement.
///
/// See IEEE 1076-2008 section 10.7.
#[derive(Debug)]
pub struct CallStmt {
	/// The target subprogram.
	pub subprog: SubprogRef,
	/// The optional call parameters.
	pub params: (),
}

/// An if statement.
///
/// See IEEE 1076-2008 section 10.8.
#[derive(Debug)]
pub struct IfStmt {
	/// The condition and statements of each branch.
	pub branches: Vec<(ExprRef, Vec<SeqStmtRef>)>,
	/// The optional else branch.
	pub otherwise: Option<Vec<SeqStmtRef>>,
}

/// A case statement.
///
/// See IEEE 1076-2008 section 10.9.
#[derive(Debug)]
pub struct CaseStmt {
	/// Whether this is a matching case statement (indicated by `?`).
	pub matching: bool,
	/// The expression being switched over.
	pub switch: ExprRef,
	/// The cases.
	pub cases: Vec<(Spanned<Choices>, Vec<SeqStmtRef>)>,
}

/// A loop statement.
///
/// See IEEE 1076-2008 section 10.10.
#[derive(Debug)]
pub struct LoopStmt {
	/// The loop scheme.
	pub scheme: LoopScheme,
	/// The loop statements.
	pub stmts: Vec<SeqStmtRef>,
}

/// A loop scheme.
///
/// See IEEE 1076-2008 section 10.10.
#[derive(Debug)]
pub enum LoopScheme {
	/// An infinite loop.
	Loop,
	/// A while loop.
	While(ExprRef),
	/// A for loop.
	For(Spanned<Name>, Spanned<DiscreteRange>),
}

/// A next or exit statement.
///
/// See IEEE 1076-2008 section 10.11 and 10.12.
#[derive(Debug)]
pub struct NexitStmt {
	/// Whether this is a next or exit statement.
	pub mode: NexitMode,
	/// The optional loop the statement operates on. If omitted the statement
	/// applies to the innermost loop.
	pub target: Option<Spanned<LoopStmtRef>>,
	/// The optional condition.
	pub cond: Option<ExprRef>,
}

/// A discriminant for next/exit statements.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum NexitMode {
	/// A next statement.
	Next,
	/// An exit statement.
	Exit,
}

/// A return statement.
///
/// See IEEE 1076-2008 section 10.13.
#[derive(Debug)]
pub struct ReturnStmt {
	/// The optional return value.
	pub expr: Option<ExprRef>,
}

/// A null statement.
///
/// See IEEE 1076-2008 section 10.14.
#[derive(Debug)]
pub struct NullStmt;

/// A sensitivity list.
///
/// See IEEE 1076-2008 section 10.2.
pub type SensitivityList = Vec<Spanned<SignalRef>>;

/// A target.
///
/// See IEEE 1076-2008 section 10.5.2.1.
#[derive(Debug)]
pub enum Target {
	Name(ExprRef),
	Aggregate(AggregateRef),
}

/// An aggregate.
///
/// See IEEE 1076-2008 section 9.3.3.1.
#[derive(Debug)]
pub struct Aggregate {
	/// The parent scope.
	pub parent: ScopeRef,
	/// The span the aggregate covers in the source file.
	pub span: Span,
	/// The positional fields of the aggregate.
	pub positional: Vec<Spanned<ExprRef>>,
	/// The named fields of the aggregate.
	pub named: AggregateKind,
	/// The `others` field of the aggregate.
	pub others: Option<Spanned<ExprRef>>,
}

/// A list of choices used in aggregates, selected assignments, and case
/// statements.
///
/// See IEEE 1076-2008 section 9.3.3.1.
pub type Choices = Vec<Spanned<Choice>>;

/// A choice in an aggregate.
///
/// See IEEE 1076-2008 section 9.3.3.1.
#[derive(Debug)]
pub enum Choice {
	/// An expression.
	Expr(ExprRef),
	/// A discrete range.
	DiscreteRange(DiscreteRange),
	/// A record element.
	Element(Name),
	/// The keyword `others`.
	Others
}

impl Choice {
	/// Check if the choice is `others`.
	pub fn is_others(&self) -> bool {
		match *self {
			Choice::Others => true,
			_ => false,
		}
	}

	/// Check if the choice is a record element.
	pub fn is_element(&self) -> bool {
		match *self {
			Choice::Element(_) => true,
			_ => false,
		}
	}
}

/// A list of choices used in record aggregates.
pub type RecordChoices = Vec<Spanned<Name>>;

/// A list of choices used in array aggregates.
pub type ArrayChoices = Vec<Spanned<ArrayChoice>>;

/// A choice in an array aggregate.
#[derive(Debug)]
pub enum ArrayChoice {
	/// An expression.
	Expr(ExprRef),
	/// A discrete range.
	DiscreteRange(DiscreteRange),
}

/// An aggregate kind.
///
/// This determines whether the named elements make the aggregate a record or an
/// array aggregate.
#[derive(Debug)]
pub enum AggregateKind {
	/// The aggregate has no named elements and can be both.
	Both,
	/// A record aggregate.
	Record(Vec<Spanned<(RecordChoices, Spanned<ExprRef>)>>),
	/// An array aggregate.
	Array(Vec<Spanned<(ArrayChoices, Spanned<ExprRef>)>>),
}

/// An association list.
///
/// See IEEE 1076-2008 section 6.5.7.
pub type AssocList = Vec<AssocElement>;

/// An association element.
#[derive(Debug)]
pub struct AssocElement {
	/// The span the element covers in the source file.
	pub span: Span,
	/// The optional formal part.
	pub formal: Option<Spanned<ExprRef>>,
	/// The actual part.
	pub actual: Spanned<AssocActual>,
}

/// An actual part of an association element.
#[derive(Debug)]
pub enum AssocActual {
	/// An expression or name.
	Expr(ExprRef),
	/// An expression with leading `inertial` keyword.
	InertialExpr(ExprRef),
	/// A subtype indication.
	Subtype(SubtypeIndRef),
	/// An open association.
	Open,
}
