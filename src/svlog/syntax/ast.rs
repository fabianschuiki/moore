// Copyright (c) 2016-2020 Fabian Schuiki

//! An abstract syntax tree for SystemVerilog.

#![allow(unused_variables)]

use crate::token::{Lit, Op};
use moore_common::{
    name::Name,
    source::{Span, Spanned, INVALID_SPAN},
    util::{HasDesc, HasSpan},
};
use moore_derive::{AcceptVisitor, CommonNode};
use std::cell::Cell;

/// An AST node.
pub trait AnyNode<'a>: BasicNode<'a> + std::fmt::Binary {
    /// Get this node's span in the input.
    fn span(&self) -> Span;

    /// Get this node's parent.
    fn get_parent(&self) -> Option<&'a dyn AnyNode<'a>> {
        None
    }

    /// Link up this node.
    fn link(&'a self, parent: Option<&'a dyn AnyNode<'a>>, order: &mut usize) {}
}

/// Basic attribute of an AST node.
///
/// If this trait is present on `Node<T>`, then `Node<T>` will automatically
/// implement the full `AnyNode` trait.
pub trait BasicNode<'a>: std::fmt::Debug + ForEachChild<'a> + ForEachNode<'a> {
    /// Get the type name of the node.
    fn type_name(&self) -> &'static str;

    /// Convert this node to the exhaustive `AllNode` enum.
    fn as_all(&'a self) -> AllNode<'a>;

    /// Convert this node to an `AnyNode` trait object.
    fn as_any(&'a self) -> &'a dyn AnyNode<'a>;
}

/// A node which allows iterating over each child node.
pub trait ForEachChild<'a> {
    /// Apply a function to each child node.
    fn for_each_child(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>));
}

/// A node which can pass itself as `AnyNode` to a callback.
pub trait ForEachNode<'a> {
    /// Apply a function to this node.
    fn for_each_node(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>)) {}
}

impl<'a, T> ForEachNode<'a> for Option<T>
where
    T: ForEachNode<'a>,
{
    fn for_each_node(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>)) {
        if let Some(node) = self {
            node.for_each_node(each);
        }
    }
}

impl<'a, T> ForEachNode<'a> for Vec<T>
where
    T: ForEachNode<'a>,
{
    fn for_each_node(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>)) {
        for node in self {
            node.for_each_node(each);
        }
    }
}

impl<'a, T> ForEachNode<'a> for Spanned<T>
where
    T: ForEachNode<'a>,
{
    fn for_each_node(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>)) {
        self.value.for_each_node(each);
    }
}

impl<'a> ForEachNode<'a> for Span {}
impl<'a> ForEachNode<'a> for Name {}
impl<'a> ForEachNode<'a> for Lit {}
impl<'a> ForEachNode<'a> for bool {}

impl<'a> ForEachNode<'a> for Stmt<'a> {}
impl<'a> ForEachNode<'a> for StmtData<'a> {}
impl<'a> ForEachNode<'a> for GenerateBlock<'a> {}

/// Common interface to all AST nodes.
pub trait CommonNode {
    /// Apply a function to each child node.
    fn for_each_child(&self, f: &mut dyn FnMut(&dyn CommonNode));
}

impl<T> CommonNode for Vec<T>
where
    T: CommonNode,
{
    fn for_each_child(&self, f: &mut dyn FnMut(&dyn CommonNode)) {
        for c in self {
            f(c)
        }
    }
}

impl<T> CommonNode for Option<T>
where
    T: CommonNode,
{
    fn for_each_child(&self, f: &mut dyn FnMut(&dyn CommonNode)) {
        if let Some(c) = self {
            f(c)
        }
    }
}

/// Common denominator across all AST nodes.
#[derive(Clone)]
pub struct Node<'a, T> {
    /// Full span the node covers in the input.
    pub span: Span,
    /// Parent node.
    pub parent: Cell<Option<&'a dyn AnyNode<'a>>>,
    /// Lexical order of the node.
    pub order: Cell<usize>,
    /// Lexical predecessor node.
    pub lex_pred: Cell<Option<&'a ()>>,
    /// Lexical successor node.
    pub lex_succ: Cell<Option<&'a ()>>,
    /// Per-node data.
    pub data: T,
}

impl<'a, T> Node<'a, T> {
    /// Create a new AST node.
    pub fn new(span: Span, data: T) -> Self {
        Node {
            span,
            data,
            parent: Default::default(),
            order: Default::default(),
            lex_pred: Default::default(),
            lex_succ: Default::default(),
        }
    }
}

/// Automatically implement `AnyNode` for `Node<T>` if enough information is
/// present.
impl<'a, T> AnyNode<'a> for Node<'a, T>
where
    Self: BasicNode<'a> + std::fmt::Binary,
    T: std::fmt::Debug + ForEachChild<'a>,
{
    fn span(&self) -> Span {
        self.span
    }

    fn get_parent(&self) -> Option<&'a dyn AnyNode<'a>> {
        self.parent.get()
    }

    fn link(&'a self, parent: Option<&'a dyn AnyNode<'a>>, order: &mut usize) {
        trace!("Linking {:b}", self);
        self.parent.set(parent);
        self.order.set(*order);
        *order += 1;
        self.for_each_child(&mut |node| {
            node.link(Some(self.as_any()), order);
        });
    }
}

impl<'a, T> std::fmt::Debug for Node<'a, T>
where
    Self: BasicNode<'a> + std::fmt::Binary,
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct(self.type_name())
            .field("handle", &format_args!("{:b}", self))
            .field("span", &self.span)
            .field(
                "parent",
                &format_args!(
                    "{}",
                    match self.parent.get() {
                        Some(parent) => format!("{:b}", parent),
                        None => format!("<none>"),
                    }
                ),
            )
            .field("order", &format_args!("{}", self.order.get()))
            .field("data", &self.data)
            .finish()
    }
}

impl<'a, T> std::fmt::Binary for Node<'a, T>
where
    Self: BasicNode<'a>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} #{:p}", self.type_name(), self as *const _)
    }
}

impl<'a, T> CommonNode for Node<'a, T>
where
    T: CommonNode,
{
    fn for_each_child(&self, f: &mut dyn FnMut(&dyn CommonNode)) {
        self.data.for_each_child(f)
    }
}

impl<'a, T> ForEachChild<'a> for Node<'a, T>
where
    T: ForEachChild<'a>,
{
    fn for_each_child(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>)) {
        self.data.for_each_child(each)
    }
}

impl<'a, T> ForEachNode<'a> for Node<'a, T>
where
    Node<'a, T>: AnyNode<'a>,
{
    fn for_each_node(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>)) {
        each(self);
    }
}

impl<'a, 'b: 'a, T> AcceptVisitor<'a> for Node<'b, T>
where
    T: AcceptVisitor<'a>,
{
    fn accept<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {
        self.data.accept(visitor)
    }
}

impl<'a, T> std::ops::Deref for Node<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.data
    }
}

impl<'a, T> std::ops::DerefMut for Node<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.data
    }
}

impl<'a, T> PartialEq for Node<'a, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.span == other.span && self.data == other.data
    }
}

impl<'a, T> Eq for Node<'a, T> where T: Eq {}

/// A node that accepts `Visitor`s.
pub trait AcceptVisitor<'a> {
    /// Walk a visitor over the contents of `self`.
    fn accept<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V);
}

impl<'a, T> AcceptVisitor<'a> for Vec<T>
where
    T: AcceptVisitor<'a>,
{
    fn accept<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {
        for c in self {
            c.accept(visitor);
        }
    }
}

impl<'a, T> AcceptVisitor<'a> for Option<T>
where
    T: AcceptVisitor<'a>,
{
    fn accept<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {
        if let Some(c) = self {
            c.accept(visitor);
        }
    }
}

impl<'a, T> AcceptVisitor<'a> for Spanned<T>
where
    T: AcceptVisitor<'a>,
{
    fn accept<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {
        self.value.accept(visitor);
    }
}

/// A node that walks a `Visitor` over itself.
pub trait WalkVisitor<'a> {
    /// Walk a visitor over `self`.
    fn walk<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V);
}

impl<'a, T> WalkVisitor<'a> for Vec<T>
where
    T: WalkVisitor<'a>,
{
    fn walk<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {
        for c in self {
            c.walk(visitor);
        }
    }
}

impl<'a, T> WalkVisitor<'a> for Option<T>
where
    T: WalkVisitor<'a>,
{
    fn walk<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {
        if let Some(c) = self {
            c.walk(visitor);
        }
    }
}

impl<'a, T> WalkVisitor<'a> for Spanned<T>
where
    T: WalkVisitor<'a>,
{
    fn walk<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {
        self.value.walk(visitor);
    }
}

impl<'a> WalkVisitor<'a> for Span {
    fn walk<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {}
}

impl<'a> WalkVisitor<'a> for Name {
    fn walk<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {}
}

impl<'a> WalkVisitor<'a> for Lit {
    fn walk<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {}
}

impl<'a> WalkVisitor<'a> for bool {
    fn walk<V: Visitor<'a> + ?Sized>(&'a self, visitor: &mut V) {}
}

pub use self::ExprData::*;
pub use self::StmtData::*;
pub use self::TypeData::*;

// Deprecated names.
pub type ModDecl<'a> = Module<'a>;
pub type IntfDecl<'a> = Interface<'a>;
pub type PackageDecl<'a> = Package<'a>;

/// An entire design file.
#[moore_derive::node]
#[derive(Debug)]
pub struct Root<'a> {
    pub timeunits: Timeunit,
    pub items: Vec<Item<'a>>,
}

#[allow(dead_code)]
fn checks1<'a>(ast: &'a Root<'a>, v: &mut impl Visitor<'a>) {
    ast.accept(v);
}

/// An item that may appear in a hierarchical scope.
///
/// This includes the following:
/// - root scope
/// - modules
/// - interfaces
/// - packages
/// - classes
/// - generates
#[moore_derive::node]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Item<'a> {
    Dummy,
    ModuleDecl(Module<'a>),
    InterfaceDecl(Interface<'a>),
    PackageDecl(Package<'a>),
    #[dont_visit]
    ClassDecl(ClassDecl<'a>),
    #[dont_visit]
    ProgramDecl(()),
    ImportDecl(ImportDecl),
    #[dont_visit]
    ParamDecl(ParamDecl<'a>),
    #[dont_visit]
    ModportDecl(ModportDecl),
    #[dont_visit]
    Typedef(Typedef<'a>),
    #[dont_visit]
    PortDecl(PortDecl<'a>),
    #[dont_visit]
    Procedure(Procedure<'a>),
    #[dont_visit]
    SubroutineDecl(SubroutineDecl<'a>),
    #[dont_visit]
    ContAssign(ContAssign<'a>),
    #[dont_visit]
    GenvarDecl(Vec<GenvarDecl<'a>>),
    #[dont_visit]
    GenerateRegion(Span, Vec<Item<'a>>),
    #[dont_visit]
    GenerateFor(GenerateFor<'a>),
    #[dont_visit]
    GenerateIf(GenerateIf<'a>),
    #[dont_visit]
    GenerateCase(GenerateCase),
    #[dont_visit]
    Assertion(Assertion<'a>),
    NetDecl(NetDecl<'a>),
    VarDecl(VarDecl<'a>),
    #[dont_visit]
    Inst(Inst<'a>),
}

impl HasSpan for Item<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        match &self.data {
            ItemData::ModuleDecl(x) => x.human_span(),
            _ => self.span,
        }
    }
}

impl HasDesc for Item<'_> {
    fn desc(&self) -> &'static str {
        match &self.data {
            ItemData::ModuleDecl(x) => x.desc(),
            ItemData::InterfaceDecl(_) => "interface declaration",
            ItemData::PackageDecl(_) => "package declaration",
            ItemData::ImportDecl(_) => "import declaration",
            ItemData::ParamDecl(_) => "parameter declaration",
            ItemData::ProgramDecl(_) => "program declaration",
            ItemData::ModportDecl(_) => "modport declaration",
            ItemData::ClassDecl(_) => "class declaration",
            ItemData::PortDecl(_) => "port declaration",
            ItemData::Procedure(_) => "procedure declaration",
            ItemData::SubroutineDecl(_) => "subroutine declaration",
            ItemData::Assertion(_) => "assertion",
            ItemData::NetDecl(_) => "net declaration",
            ItemData::VarDecl(_) => "variable declaration",
            ItemData::Inst(_) => "instantiation",
            _ => "<invalid item>",
        }
    }

    fn desc_full(&self) -> String {
        match &self.data {
            ItemData::ModuleDecl(x) => x.desc_full(),
            _ => self.desc().into(),
        }
    }
}

/// A module.
#[moore_derive::node]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module<'a> {
    pub lifetime: Lifetime, // default static
    pub name: Name,
    pub name_span: Span,
    pub imports: Vec<ImportDecl>,
    #[dont_visit]
    pub params: Vec<ParamDecl<'a>>,
    #[dont_visit]
    pub ports: Vec<Port<'a>>,
    pub items: Vec<Item<'a>>,
}

impl HasSpan for Module<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name_span
    }
}

impl HasDesc for Module<'_> {
    fn desc(&self) -> &'static str {
        "module declaration"
    }

    fn desc_full(&self) -> String {
        format!("module `{}`", self.name)
    }
}

/// An interface.
#[moore_derive::node]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interface<'a> {
    pub lifetime: Lifetime, // default static
    pub name: Name,
    pub name_span: Span,
    #[dont_visit]
    pub params: Vec<ParamDecl<'a>>,
    #[dont_visit]
    pub ports: Vec<Port<'a>>,
    pub items: Vec<Item<'a>>,
}

impl HasSpan for Interface<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name_span
    }
}

impl HasDesc for Interface<'_> {
    fn desc(&self) -> &'static str {
        "interface declaration"
    }

    fn desc_full(&self) -> String {
        format!("interface `{}`", self.name)
    }
}

/// A package.
#[moore_derive::node]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Package<'a> {
    pub lifetime: Lifetime,
    pub name: Name,
    pub name_span: Span,
    pub timeunits: Timeunit,
    pub items: Vec<Item<'a>>,
}

impl HasSpan for Package<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name_span
    }
}

impl HasDesc for Package<'_> {
    fn desc(&self) -> &'static str {
        "package declaration"
    }

    fn desc_full(&self) -> String {
        format!("package `{}`", self.name)
    }
}

/// Lifetime specifier for variables, tasks, and functions. Defaults to static.
#[moore_derive::visit]
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
#[moore_derive::visit]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Timeunit {
    pub unit: Option<Spanned<Lit>>,
    pub prec: Option<Spanned<Lit>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type<'a> {
    pub span: Span,
    pub data: TypeData<'a>,
    pub sign: TypeSign,
    pub dims: Vec<TypeDim<'a>>,
}

impl HasSpan for Type<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Type<'_> {
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
pub enum TypeData<'a> {
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
        ty: Box<Type<'a>>,
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
    EnumType(Option<Box<Type<'a>>>, Vec<EnumName<'a>>),
    StructType {
        kind: StructKind,
        packed: bool,
        signing: TypeSign,
        members: Vec<StructMember<'a>>,
    },

    // Specialization
    SpecializedType(Box<Type<'a>>, Vec<ParamAssignment<'a>>),

    /// Type reference, such as `type(x)` or `type(int)`.
    TypeRef(Box<TypeOrExpr<'a>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum TypeSign {
    None,
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDim<'a> {
    Expr(Expr<'a>),
    Range(Expr<'a>, Expr<'a>),
    Queue(Option<Expr<'a>>),
    Unsized,
    Associative(Option<Type<'a>>),
}

impl HasDesc for TypeDim<'_> {
    fn desc(&self) -> &'static str {
        "type dimension"
    }

    fn desc_full(&self) -> String {
        match *self {
            TypeDim::Expr(ref expr) => format!("`[{}]`", expr.span.extract()),
            TypeDim::Range(ref lhs, ref rhs) => {
                format!("`[{}:{}]`", lhs.span.extract(), rhs.span.extract())
            }
            TypeDim::Queue(None) => format!("`[$]`"),
            TypeDim::Queue(Some(ref expr)) => format!("`[$:{}]`", expr.span.extract()),
            TypeDim::Unsized => format!("`[]`"),
            TypeDim::Associative(None) => format!("[*]"),
            TypeDim::Associative(Some(ref ty)) => format!("[{}]", ty.span.extract()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumName<'a> {
    pub span: Span,
    pub name: Identifier,
    pub range: Option<Expr<'a>>,
    pub value: Option<Expr<'a>>,
}

impl HasSpan for EnumName<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for EnumName<'_> {
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
pub struct StructMember<'a> {
    pub span: Span,
    pub rand_qualifier: Option<RandomQualifier>,
    pub ty: Box<Type<'a>>,
    pub names: Vec<VarDeclName<'a>>,
}

impl HasSpan for StructMember<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for StructMember<'_> {
    fn desc(&self) -> &'static str {
        "struct member"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Port<'a> {
    Intf {
        span: Span,
        modport: Option<Identifier>,
        name: Identifier,
        dims: Vec<TypeDim<'a>>,
        expr: Option<Expr<'a>>,
    },
    Explicit {
        span: Span,
        dir: Option<PortDir>,
        name: Identifier,
        expr: Option<Expr<'a>>,
    },
    Named {
        span: Span,
        dir: Option<PortDir>,
        kind: Option<PortKind>,
        ty: Type<'a>,
        name: Identifier,
        dims: Vec<TypeDim<'a>>,
        expr: Option<Expr<'a>>,
    },
    Implicit(Expr<'a>),
}

impl HasSpan for Port<'_> {
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

impl HasDesc for Port<'_> {
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
pub struct PortDecl<'a> {
    pub span: Span,
    pub dir: PortDir,
    pub kind: Option<PortKind>,
    pub ty: Type<'a>,
    pub names: Vec<VarDeclName<'a>>,
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
pub struct Procedure<'a> {
    pub span: Span,
    pub kind: ProcedureKind,
    pub stmt: Stmt<'a>,
}

impl HasSpan for Procedure<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Procedure<'_> {
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
pub struct Stmt<'a> {
    pub span: Span,
    #[ignore_child]
    pub label: Option<Name>,
    pub data: StmtData<'a>,
}

impl HasSpan for Stmt<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Stmt<'_> {
    fn desc(&self) -> &'static str {
        "statement"
    }
}

#[derive(CommonNode, Debug, Clone, PartialEq, Eq)]
pub enum StmtData<'a> {
    NullStmt,
    SequentialBlock(Vec<Stmt<'a>>),
    ParallelBlock(Vec<Stmt<'a>>, JoinKind),
    IfStmt {
        up: Option<UniquePriority>,
        cond: Expr<'a>,
        main_stmt: Box<Stmt<'a>>,
        else_stmt: Option<Box<Stmt<'a>>>,
    },
    BlockingAssignStmt {
        lhs: Expr<'a>,
        rhs: Expr<'a>,
        op: AssignOp,
    },
    NonblockingAssignStmt {
        lhs: Expr<'a>,
        rhs: Expr<'a>,
        delay: Option<DelayControl<'a>>,
        event: Option<()>,
    },
    TimedStmt(TimingControl<'a>, Box<Stmt<'a>>),
    CaseStmt {
        up: Option<UniquePriority>,
        kind: CaseKind,
        expr: Expr<'a>,
        mode: CaseMode,
        items: Vec<CaseItem<'a>>,
    },
    ForeverStmt(Box<Stmt<'a>>),
    RepeatStmt(Expr<'a>, Box<Stmt<'a>>),
    WhileStmt(Expr<'a>, Box<Stmt<'a>>),
    DoStmt(Box<Stmt<'a>>, Expr<'a>),
    ForStmt(Box<Stmt<'a>>, Expr<'a>, Expr<'a>, Box<Stmt<'a>>),
    ForeachStmt(Expr<'a>, Vec<Option<Identifier>>, Box<Stmt<'a>>),
    ExprStmt(Expr<'a>),
    VarDeclStmt(VarDecl<'a>),
    GenvarDeclStmt(Vec<GenvarDecl<'a>>),
    ContinueStmt,
    BreakStmt,
    ReturnStmt(Option<Expr<'a>>),
    ImportStmt(ImportDecl),
    AssertionStmt(Box<Assertion<'a>>),
    WaitExprStmt(Expr<'a>, Box<Stmt<'a>>),
    WaitForkStmt,
    DisableForkStmt,
    DisableStmt(Name),
}

impl<'a> Stmt<'a> {
    pub fn new_null(span: Span) -> Stmt<'a> {
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
pub enum CaseItem<'a> {
    Default(Box<Stmt<'a>>),
    Expr(Vec<Expr<'a>>, Box<Stmt<'a>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DelayControl<'a> {
    pub span: Span,
    pub expr: Expr<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventControl<'a> {
    pub span: Span,
    pub data: EventControlData<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventControlData<'a> {
    Implicit,
    Expr(EventExpr<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CycleDelay {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimingControl<'a> {
    Delay(DelayControl<'a>),
    Event(EventControl<'a>),
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

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDecl<'a> {
    pub span: Span,
    pub konst: bool,
    pub var: bool,
    pub lifetime: Option<Lifetime>,
    #[dont_visit]
    pub ty: Type<'a>,
    pub names: Vec<VarDeclName<'a>>,
}

impl HasSpan for VarDecl<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for VarDecl<'_> {
    fn desc(&self) -> &'static str {
        "variable declaration"
    }
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDeclName<'a> {
    pub span: Span,
    pub name: Name,
    pub name_span: Span,
    #[dont_visit]
    pub dims: Vec<TypeDim<'a>>,
    pub init: Option<Expr<'a>>,
}

impl HasSpan for VarDeclName<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name_span
    }
}

impl HasDesc for VarDeclName<'_> {
    fn desc(&self) -> &'static str {
        "variable"
    }

    fn desc_full(&self) -> String {
        format!("variable `{}`", self.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenvarDecl<'a> {
    pub span: Span,
    pub name: Name,
    pub name_span: Span,
    pub init: Option<Expr<'a>>,
}

impl HasSpan for GenvarDecl<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name_span
    }
}

impl HasDesc for GenvarDecl<'_> {
    fn desc(&self) -> &'static str {
        "genvar"
    }

    fn desc_full(&self) -> String {
        format!("genvar `{}`", self.name)
    }
}

/// An expression.
#[moore_derive::node]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr<'a> {
    DummyExpr,
    LiteralExpr(Lit),
    #[dont_visit]
    IdentExpr(Identifier),
    #[dont_visit]
    SysIdentExpr(Identifier),
    #[dont_visit]
    ScopeExpr(Box<Expr<'a>>, Identifier),
    #[dont_visit]
    IndexExpr {
        indexee: Box<Expr<'a>>,
        index: Box<Expr<'a>>,
    },
    #[dont_visit]
    UnaryExpr {
        op: Op,
        expr: Box<Expr<'a>>,
        postfix: bool,
    },
    #[dont_visit]
    BinaryExpr {
        op: Op,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
    #[dont_visit]
    TernaryExpr {
        cond: Box<Expr<'a>>,
        true_expr: Box<Expr<'a>>,
        false_expr: Box<Expr<'a>>,
    },
    #[dont_visit]
    AssignExpr {
        op: AssignOp,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
    #[dont_visit]
    #[dont_visit]
    CallExpr(Box<Expr<'a>>, Vec<CallArg<'a>>),
    #[dont_visit]
    TypeExpr(Box<Type<'a>>), // TODO: Check if this is still needed, otherwise remove
    #[dont_visit]
    ConstructorCallExpr(Vec<CallArg<'a>>),
    #[dont_visit]
    ClassNewExpr(Option<Box<Expr<'a>>>),
    #[dont_visit]
    ArrayNewExpr(Box<Expr<'a>>, Option<Box<Expr<'a>>>),
    #[dont_visit]
    EmptyQueueExpr,
    #[dont_visit]
    StreamConcatExpr {
        slice: Option<StreamConcatSlice<'a>>,
        exprs: Vec<StreamExpr<'a>>,
    },
    #[dont_visit]
    ConcatExpr {
        repeat: Option<Box<Expr<'a>>>,
        exprs: Vec<Expr<'a>>,
    },
    #[dont_visit]
    MinTypMaxExpr {
        min: Box<Expr<'a>>,
        typ: Box<Expr<'a>>,
        max: Box<Expr<'a>>,
    },
    #[dont_visit]
    RangeExpr {
        mode: RangeMode,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
    #[dont_visit]
    MemberExpr {
        expr: Box<Expr<'a>>,
        name: Identifier,
    },
    #[dont_visit]
    PatternExpr(Vec<PatternField<'a>>),
    #[dont_visit]
    InsideExpr(Box<Expr<'a>>, Vec<ValueRange<'a>>),
    #[dont_visit]
    CastExpr(Type<'a>, Box<Expr<'a>>),
    #[dont_visit]
    CastSizeExpr(Box<Expr<'a>>, Box<Expr<'a>>),
    #[dont_visit]
    CastSignExpr(Spanned<TypeSign>, Box<Expr<'a>>),
}

impl HasSpan for Expr<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for Expr<'_> {
    fn desc(&self) -> &'static str {
        "expression"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeOrExpr<'a> {
    Type(Type<'a>),
    Expr(Expr<'a>),
}

impl HasSpan for TypeOrExpr<'_> {
    fn span(&self) -> Span {
        match *self {
            TypeOrExpr::Type(ref x) => x.span(),
            TypeOrExpr::Expr(ref x) => x.span,
        }
    }

    fn human_span(&self) -> Span {
        match *self {
            TypeOrExpr::Type(ref x) => x.human_span(),
            TypeOrExpr::Expr(ref x) => x.human_span(),
        }
    }
}

impl HasDesc for TypeOrExpr<'_> {
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
pub enum ValueRange<'a> {
    Single(Expr<'a>),
    Range {
        lo: Expr<'a>,
        hi: Expr<'a>,
        span: Span,
    },
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
pub struct CallArg<'a> {
    pub span: Span,
    pub name_span: Span,
    pub name: Option<Name>,
    pub expr: Option<Expr<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StreamConcatSlice<'a> {
    Expr(Box<Expr<'a>>),
    Type(Type<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StreamExpr<'a> {
    pub expr: Box<Expr<'a>>,
    pub range: Option<Box<Expr<'a>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventExpr<'a> {
    Edge {
        span: Span,
        edge: EdgeIdent,
        value: Expr<'a>,
    },
    Iff {
        span: Span,
        expr: Box<EventExpr<'a>>,
        cond: Expr<'a>,
    },
    Or {
        span: Span,
        lhs: Box<EventExpr<'a>>,
        rhs: Box<EventExpr<'a>>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeIdent {
    Implicit,
    Edge,
    Posedge,
    Negedge,
}

impl HasSpan for EventExpr<'_> {
    fn span(&self) -> Span {
        match *self {
            EventExpr::Edge { span: sp, .. } => sp,
            EventExpr::Iff { span: sp, .. } => sp,
            EventExpr::Or { span: sp, .. } => sp,
        }
    }
}

impl HasDesc for EventExpr<'_> {
    fn desc(&self) -> &'static str {
        "event expression"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassDecl<'a> {
    pub span: Span,
    pub virt: bool,
    pub lifetime: Lifetime, // default static
    pub name: Identifier,
    pub params: Vec<ParamDecl<'a>>,
    pub extends: Option<(Type<'a>, Vec<CallArg<'a>>)>,
    pub impls: Vec<Identifier>,
    pub items: Vec<ClassItem<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassItem<'a> {
    pub span: Span,
    pub qualifiers: Vec<(ClassItemQualifier, Span)>,
    pub data: ClassItemData<'a>,
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
pub enum ClassItemData<'a> {
    Property,
    Typedef(Typedef<'a>),
    SubroutineDecl(SubroutineDecl<'a>),
    ExternSubroutine(SubroutinePrototype<'a>),
    Constraint(Constraint<'a>),
    ClassDecl,
    CovergroupDecl,
    ParamDecl(ParamDecl<'a>),
    Null,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RandomQualifier {
    Rand,
    Randc,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Typedef<'a> {
    pub span: Span,
    pub name: Identifier,
    pub ty: Type<'a>,
    pub dims: Vec<TypeDim<'a>>,
}

impl HasSpan for Typedef<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for Typedef<'_> {
    fn desc(&self) -> &'static str {
        "typedef"
    }

    fn desc_full(&self) -> String {
        format!("typedef `{}`", self.name.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint<'a> {
    pub span: Span,
    pub kind: ConstraintKind,
    pub statik: bool,
    pub name: Name,
    pub name_span: Span,
    pub items: Vec<ConstraintItem<'a>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    Decl,
    Proto,
    ExternProto,
    PureProto,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintItem<'a> {
    pub span: Span,
    pub data: ConstraintItemData<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintItemData<'a> {
    If,
    Foreach,
    Expr(Expr<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutineDecl<'a> {
    pub span: Span,
    pub prototype: SubroutinePrototype<'a>,
    pub items: Vec<SubroutineItem<'a>>,
}

impl HasSpan for SubroutineDecl<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.prototype.name.span
    }
}

impl HasDesc for SubroutineDecl<'_> {
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
pub struct SubroutinePrototype<'a> {
    pub span: Span,
    pub kind: SubroutineKind,
    pub lifetime: Option<Lifetime>,
    pub name: Identifier,
    pub args: Vec<SubroutinePort<'a>>,
    pub retty: Option<Type<'a>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SubroutineKind {
    Func,
    Task,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePort<'a> {
    pub span: Span,
    pub dir: Option<SubroutinePortDir>,
    pub var: bool,
    pub ty: Type<'a>,
    pub name: Option<SubroutinePortName<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePortName<'a> {
    pub name: Identifier,
    pub dims: Vec<TypeDim<'a>>,
    pub expr: Option<Expr<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubroutineItem<'a> {
    PortDecl(SubroutinePortDecl<'a>),
    Stmt(Stmt<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePortDecl<'a> {
    pub span: Span,
    pub dir: SubroutinePortDir,
    pub var: bool,
    pub ty: Type<'a>,
    pub names: Vec<VarDeclName<'a>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubroutinePortDir {
    Input,
    Output,
    Inout,
    Ref,
    ConstRef,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NetDecl<'a> {
    pub span: Span,
    #[dont_visit]
    pub net_type: NetType,
    #[dont_visit]
    pub strength: Option<NetStrength>,
    #[dont_visit]
    pub kind: NetKind,
    #[dont_visit]
    pub ty: Type<'a>,
    #[dont_visit]
    pub delay: Option<DelayControl<'a>>,
    pub names: Vec<VarDeclName<'a>>,
}

impl HasSpan for NetDecl<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for NetDecl<'_> {
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
pub struct PatternField<'a> {
    pub span: Span,
    pub data: PatternFieldData<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternFieldData<'a> {
    Default(Box<Expr<'a>>),
    Member(Box<Expr<'a>>, Box<Expr<'a>>),
    Type(Type<'a>, Box<Expr<'a>>),
    Expr(Box<Expr<'a>>),
    Repeat(Box<Expr<'a>>, Vec<Expr<'a>>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl {
    pub span: Span,
    pub items: Vec<ImportItem>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportItem {
    pub span: Span,
    pub pkg: Spanned<Name>,
    pub name: Option<Spanned<Name>>, // None means `import pkg::*`
}

impl HasSpan for ImportItem {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for ImportItem {
    fn desc(&self) -> &'static str {
        "import"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assertion<'a> {
    pub span: Span,
    pub label: Option<(Name, Span)>,
    pub data: AssertionData<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionData<'a> {
    Immediate(BlockingAssertion<'a>),
    Deferred(AssertionDeferred, BlockingAssertion<'a>),
    Concurrent(ConcurrentAssertion<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionDeferred {
    /// `assert #0`
    Observed,
    /// `assert final`
    Final,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockingAssertion<'a> {
    Assert(Expr<'a>, AssertionActionBlock<'a>),
    Assume(Expr<'a>, AssertionActionBlock<'a>),
    Cover(Expr<'a>, Stmt<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcurrentAssertion<'a> {
    AssertProperty(PropSpec, AssertionActionBlock<'a>),
    AssumeProperty(PropSpec, AssertionActionBlock<'a>),
    CoverProperty(PropSpec, Stmt<'a>),
    CoverSequence,
    ExpectProperty(PropSpec, AssertionActionBlock<'a>),
    RestrictProperty(PropSpec),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionActionBlock<'a> {
    Positive(Stmt<'a>),
    Negative(Stmt<'a>),
    Both(Stmt<'a>, Stmt<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeqExpr<'a> {
    pub span: Span,
    pub data: SeqExprData<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqExprData<'a> {
    Expr(Expr<'a>, Option<SeqRep<'a>>),
    BinOp(SeqBinOp, Box<SeqExpr<'a>>, Box<SeqExpr<'a>>),
    Throughout(Expr<'a>, Box<SeqExpr<'a>>),
    Clocked(EventExpr<'a>, Box<SeqExpr<'a>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqRep<'a> {
    Consec(Expr<'a>),    // [* expr]
    ConsecStar,          // [*]
    ConsecPlus,          // [+]
    Nonconsec(Expr<'a>), // [= expr]
    Goto(Expr<'a>),      // [-> expr]
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
pub struct PropExpr<'a> {
    pub span: Span,
    pub data: PropExprData<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropExprData<'a> {
    SeqOp(PropSeqOp, SeqExpr<'a>),
    SeqBinOp(PropSeqBinOp, PropSeqOp, SeqExpr<'a>, Box<PropExpr<'a>>),
    Not(Box<PropExpr<'a>>),
    BinOp(PropBinOp, Box<PropExpr<'a>>, Box<PropExpr<'a>>),
    Clocked(EventExpr<'a>, Box<PropExpr<'a>>),
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
pub struct Inst<'a> {
    pub span: Span,
    /// The name of the module to instantiate.
    pub target: Identifier,
    /// The parameters in the module to be assigned.
    pub params: Vec<ParamAssignment<'a>>,
    /// The names and ports of the module instantiations.
    pub names: Vec<InstName<'a>>,
}

impl HasSpan for Inst<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.target.span
    }
}

impl HasDesc for Inst<'_> {
    fn desc(&self) -> &'static str {
        "instantiation"
    }

    fn desc_full(&self) -> String {
        format!("`{}` instantiation", self.target.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstName<'a> {
    pub span: Span,
    pub name: Identifier,
    pub dims: Vec<TypeDim<'a>>,
    pub conns: Vec<PortConn<'a>>,
}

impl HasSpan for InstName<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for InstName<'_> {
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
pub struct ParamDecl<'a> {
    pub span: Span,
    pub local: bool,
    pub kind: ParamKind<'a>,
}

impl HasSpan for ParamDecl<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for ParamDecl<'_> {
    fn desc(&self) -> &'static str {
        "parameter"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamKind<'a> {
    Type(Vec<ParamTypeDecl<'a>>),
    Value(Vec<ParamValueDecl<'a>>),
}

/// A single type assignment within a parameter or localparam declaration.
///
/// ```text
/// ident ["=" type]
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamTypeDecl<'a> {
    pub span: Span,
    pub name: Identifier,
    pub ty: Option<Type<'a>>,
}

impl HasSpan for ParamTypeDecl<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for ParamTypeDecl<'_> {
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
pub struct ParamValueDecl<'a> {
    pub span: Span,
    pub ty: Type<'a>,
    pub name: Identifier,
    pub dims: Vec<TypeDim<'a>>,
    pub expr: Option<Expr<'a>>,
}

impl HasSpan for ParamValueDecl<'_> {
    fn span(&self) -> Span {
        self.span
    }

    fn human_span(&self) -> Span {
        self.name.span
    }
}

impl HasDesc for ParamValueDecl<'_> {
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
pub struct ContAssign<'a> {
    pub span: Span,
    pub strength: Option<(DriveStrength, DriveStrength)>,
    pub delay: Option<Expr<'a>>,
    pub delay_control: Option<DelayControl<'a>>,
    pub assignments: Vec<(Expr<'a>, Expr<'a>)>,
}

impl HasSpan for ContAssign<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for ContAssign<'_> {
    fn desc(&self) -> &'static str {
        "continuous assignment"
    }
}

#[derive(CommonNode, Debug, Clone, PartialEq, Eq)]
pub struct GenerateFor<'a> {
    pub span: Span,
    pub init: Stmt<'a>,
    #[ignore_child]
    pub cond: Expr<'a>,
    #[ignore_child]
    pub step: Expr<'a>,
    pub block: GenerateBlock<'a>,
}

impl HasSpan for GenerateFor<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for GenerateFor<'_> {
    fn desc(&self) -> &'static str {
        "for-generate statement"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateIf<'a> {
    pub span: Span,
    pub cond: Expr<'a>,
    pub main_block: GenerateBlock<'a>,
    pub else_block: Option<GenerateBlock<'a>>,
}

impl HasSpan for GenerateIf<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for GenerateIf<'_> {
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
pub struct GenerateBlock<'a> {
    pub span: Span,
    #[ignore_child]
    pub label: Option<Name>,
    #[ignore_child]
    pub items: Vec<Item<'a>>,
}

impl HasSpan for GenerateBlock<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasDesc for GenerateBlock<'_> {
    fn desc(&self) -> &'static str {
        "generate statement"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamAssignment<'a> {
    pub span: Span,
    pub name: Option<Identifier>,
    pub expr: TypeOrExpr<'a>,
}

/// A port connection as given in an instantiation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortConn<'a> {
    pub span: Span,
    pub kind: PortConnKind<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PortConnKind<'a> {
    Auto,                                // `.*` case
    Named(Identifier, PortConnMode<'a>), // `.name`, `.name()`, `.name(expr)` cases
    Positional(Expr<'a>),                // `expr` case
}

/// Represents how a named port connection is made.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PortConnMode<'a> {
    Auto,                // `.name` case
    Unconnected,         // `.name()` case
    Connected(Expr<'a>), // `.name(expr)` case
}

moore_derive::derive_visitor!();
moore_derive::derive_all_node!();
