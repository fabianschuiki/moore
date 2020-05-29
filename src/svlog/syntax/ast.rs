// Copyright (c) 2016-2020 Fabian Schuiki

//! An abstract syntax tree for SystemVerilog.

#![allow(unused_variables)]

use crate::token::{Lit, Op};
use moore_common::{
    id::NodeId,
    name::Name,
    source::{Span, Spanned},
    util::{HasDesc, HasSpan},
};
use moore_derive::{AcceptVisitor, AnyNodeData};
use std::{
    cell::Cell,
    hash::{Hash, Hasher},
};

/// An AST node.
pub trait AnyNode<'a>: BasicNode<'a> + AnyNodeData + std::fmt::Display + Send + Sync {
    /// Get this node's unique ID.
    fn id(&self) -> NodeId;

    /// Get this node's span in the input.
    fn span(&self) -> Span;

    /// Get a span that is terse and suitable to pinpoint the node for a human.
    fn human_span(&self) -> Span {
        self.span()
    }

    /// Get this node's lexical order.
    fn order(&self) -> usize;

    /// Get this node's parent.
    fn get_parent(&self) -> Option<&'a dyn AnyNode<'a>> {
        None
    }

    /// Link up this node.
    fn link(&'a self, parent: Option<&'a dyn AnyNode<'a>>, order: &mut usize) {}

    /// Link up this node as an expansion of another node.
    ///
    /// All subnodes inherit the order from their parent. Useful if a node is
    /// generated as part of a later expansion/analysis pass, but needs to hook
    /// into the AST somewhere.
    fn link_attach(&'a self, parent: &'a dyn AnyNode<'a>) {}
}

// Compare and hash nodes by reference for use in the query system.
impl<'a> Eq for &'a dyn AnyNode<'a> {}
impl<'a> PartialEq for &'a dyn AnyNode<'a> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(*self, *other)
    }
}
impl<'a> Hash for &'a dyn AnyNode<'a> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        std::ptr::hash(*self, h)
    }
}

/// Basic attributes of an AST node.
///
/// If this trait is present on `Node<T>`, then `Node<T>` will automatically
/// implement the full `AnyNode` trait.
pub trait BasicNode<'a>:
    std::fmt::Debug + AcceptVisitor<'a> + ForEachChild<'a> + ForEachNode<'a>
{
    /// Get the type name of the node.
    fn type_name(&self) -> &'static str;

    /// Convert this node to the exhaustive `AllNode` enum.
    fn as_all(&'a self) -> AllNode<'a>;

    /// Convert this node to an `AnyNode` trait object.
    fn as_any(&'a self) -> &'a dyn AnyNode<'a>;
}

/// Common details of an AST node.
pub trait AnyNodeData {
    fn as_data(&self) -> &dyn AnyNodeData
    where
        Self: Sized,
    {
        self
    }

    /// Get this node's name, or `None` if it does not have one.
    fn get_name(&self) -> Option<Spanned<Name>> {
        None
    }

    /// Describe this node for diagnostics in indefinite form, e.g. *"entity"*.
    ///
    /// This should not include any node name. Generally, we want to describe
    /// the *kind* of node to the user, for example as in *"cannot use <XYZ> at
    /// this point in the code"*.
    fn fmt_indefinite(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result;

    /// Describe this node for diagnostics in definite form, e.g. *"entity
    /// 'top'"*.
    ///
    /// If the node has a name, this should include it. Generally, we want to
    /// provide enough information for the user to pinpoint an exact node in
    /// their design.
    fn fmt_definite(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.fmt_indefinite(fmt)?;
        if let Some(name) = self.get_name() {
            write!(fmt, " `{}`", name)?
        }
        Ok(())
    }

    /// Describe this node for diagnostics in indefinite form, e.g. *"entity"*.
    fn format_indefinite(&self) -> FormatNodeIndefinite
    where
        Self: Sized,
    {
        FormatNodeIndefinite(self.as_data())
    }

    /// Describe this node for diagnostics in definite form, e.g. *"entity
    /// 'top'"*.
    fn format_definite(&self) -> FormatNodeDefinite
    where
        Self: Sized,
    {
        FormatNodeDefinite(self.as_data())
    }

    /// Describe this node for diagnostics in indefinite form, e.g. *"entity"*.
    fn to_indefinite_string(&self) -> String
    where
        Self: Sized,
    {
        self.format_indefinite().to_string()
    }

    /// Describe this node for diagnostics in definite form, e.g. *"entity
    /// 'top'"*.
    fn to_definite_string(&self) -> String
    where
        Self: Sized,
    {
        self.format_definite().to_string()
    }
}

/// Format a node in indefinite form.
pub struct FormatNodeIndefinite<'a>(&'a dyn AnyNodeData);

/// Format a node in definite form.
pub struct FormatNodeDefinite<'a>(&'a dyn AnyNodeData);

impl<'a> std::fmt::Display for FormatNodeIndefinite<'a> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.0.fmt_indefinite(fmt)
    }
}

impl<'a> std::fmt::Display for FormatNodeDefinite<'a> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.0.fmt_definite(fmt)
    }
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

impl<'a, T> ForEachNode<'a> for &'_ T
where
    T: ForEachNode<'a>,
{
    fn for_each_node(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>)) {
        (*self).for_each_node(each);
    }
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

impl<'a, T> ForEachNode<'a> for Box<T>
where
    T: ForEachNode<'a>,
{
    fn for_each_node(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>)) {
        self.as_ref().for_each_node(each);
    }
}

impl<'a> ForEachNode<'a> for Span {}
impl<'a> ForEachNode<'a> for Name {}
impl<'a> ForEachNode<'a> for Identifier {}
impl<'a> ForEachNode<'a> for Lit {}
impl<'a> ForEachNode<'a> for Op {}
impl<'a> ForEachNode<'a> for bool {}

/// Common denominator across all AST nodes.
#[derive(Clone)]
pub struct Node<'a, T> {
    /// Unique ID assigned to the node.
    pub id: NodeId,
    /// Full span the node covers in the input.
    pub span: Span,
    /// Parent node.
    pub parent: Cell<Option<&'a dyn AnyNode<'a>>>,
    /// Lexical order of the node.
    pub order: Cell<usize>,
    /// Per-node data.
    pub data: T,
}

impl<'a, T> Node<'a, T> {
    /// Create a new AST node.
    pub fn new(span: Span, data: T) -> Self {
        Node {
            id: NodeId::alloc(),
            span,
            data,
            parent: Default::default(),
            order: Default::default(),
        }
    }
}

// The following are needed due to the `Cell`s in `Node`. It is safe to share
// nodes between threads if we never change `parent` and `order` afterwards.
// We only set these cells once immediately after constructing an AST, and never
// again after.
unsafe impl<'a, T> Send for Node<'a, T> where T: Send {}
unsafe impl<'a, T> Sync for Node<'a, T> where T: Sync {}

/// Automatically implement `AnyNode` for `Node<T>` if enough information is
/// present.
impl<'a, T> AnyNode<'a> for Node<'a, T>
where
    Self: BasicNode<'a> + std::fmt::Display + AnyNodeData,
    T: std::fmt::Debug + ForEachChild<'a> + Send + Sync,
{
    fn id(&self) -> NodeId {
        self.id
    }

    fn span(&self) -> Span {
        self.span
    }

    fn order(&self) -> usize {
        self.order.get()
    }

    fn get_parent(&self) -> Option<&'a dyn AnyNode<'a>> {
        self.parent.get()
    }

    fn link(&'a self, parent: Option<&'a dyn AnyNode<'a>>, order: &mut usize) {
        trace!("Linking {:?}", self);
        self.parent.set(parent);
        self.order.set(*order);
        *order += 1;
        self.for_each_child(&mut |node| {
            node.link(Some(self.as_any()), order);
        });
    }

    fn link_attach(&'a self, parent: &'a dyn AnyNode<'a>) {
        trace!("Linking {:?} as attachment to {:?}", self, parent);
        self.parent.set(Some(parent));
        self.order.set(parent.order());
        self.for_each_child(&mut |node| {
            node.link_attach(self.as_any());
        });
    }
}

/// Automatically implement `AnyNodeData` for `Node<T>` if the inner node
/// implements it.
impl<'a, T> AnyNodeData for Node<'a, T>
where
    T: AnyNodeData,
{
    fn get_name(&self) -> Option<Spanned<Name>> {
        self.data.get_name()
    }

    fn fmt_indefinite(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.data.fmt_indefinite(fmt)
    }

    fn fmt_definite(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.data.fmt_definite(fmt)
    }
}

/// Allow any node to be printed in diagnostics in a human-friendly form.
impl<'a, T> std::fmt::Display for Node<'a, T>
where
    T: AnyNodeData,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if f.alternate() {
            self.data.fmt_indefinite(f)
        } else {
            self.data.fmt_definite(f)
        }
    }
}

/// Allow any node to be debug-formatted.
impl<'a, T> std::fmt::Debug for Node<'a, T>
where
    Self: BasicNode<'a>,
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let w = f.width().unwrap_or(0);
        if w > 0 {
            write!(f, "{:?}", self)?;
            if let Some(parent) = self.parent.get() {
                write!(f, " (#{} in {:?})", self.order.get(), parent)?;
            }
            if f.alternate() {
                write!(f, " {:#w$?}", self.data, w = (w - 1))
            } else {
                write!(f, " {:w$?}", self.data, w = (w - 1))
            }
        } else {
            write!(f, "{} #{}", self.type_name(), self.id.as_usize())
        }
    }
}

// Compare and hash nodes by reference for use in the query system.
impl<'a, T> Eq for Node<'a, T> {}
impl<'a, T> PartialEq for Node<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl<'a, T> Hash for Node<'a, T> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        std::ptr::hash(self, h)
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
    fn accept(&'a self, visitor: &mut dyn Visitor<'a>) {
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

/// A node that accepts `Visitor`s.
pub trait AcceptVisitor<'a> {
    /// Walk a visitor over the contents of `self`.
    fn accept(&'a self, visitor: &mut dyn Visitor<'a>);
}

impl<'a, T> AcceptVisitor<'a> for &'_ T
where
    T: AcceptVisitor<'a>,
{
    fn accept(&'a self, visitor: &mut dyn Visitor<'a>) {
        (*self).accept(visitor);
    }
}

impl<'a, T> AcceptVisitor<'a> for Vec<T>
where
    T: AcceptVisitor<'a>,
{
    fn accept(&'a self, visitor: &mut dyn Visitor<'a>) {
        for c in self {
            c.accept(visitor);
        }
    }
}

impl<'a, T> AcceptVisitor<'a> for Option<T>
where
    T: AcceptVisitor<'a>,
{
    fn accept(&'a self, visitor: &mut dyn Visitor<'a>) {
        if let Some(c) = self {
            c.accept(visitor);
        }
    }
}

impl<'a, T> AcceptVisitor<'a> for Spanned<T>
where
    T: AcceptVisitor<'a>,
{
    fn accept(&'a self, visitor: &mut dyn Visitor<'a>) {
        self.value.accept(visitor);
    }
}

/// A node that walks a `Visitor` over itself.
pub trait WalkVisitor<'a> {
    /// Walk a visitor over `self`.
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>);
}

impl<'a, T> WalkVisitor<'a> for &'_ T
where
    T: WalkVisitor<'a>,
{
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {
        (*self).walk(visitor);
    }
}

impl<'a, T> WalkVisitor<'a> for Vec<T>
where
    T: WalkVisitor<'a>,
{
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {
        for c in self {
            c.walk(visitor);
        }
    }
}

impl<'a, T> WalkVisitor<'a> for Option<T>
where
    T: WalkVisitor<'a>,
{
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {
        if let Some(c) = self {
            c.walk(visitor);
        }
    }
}

impl<'a, T> WalkVisitor<'a> for Spanned<T>
where
    T: WalkVisitor<'a>,
{
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {
        self.value.walk(visitor);
    }
}

impl<'a, T> WalkVisitor<'a> for Box<T>
where
    T: WalkVisitor<'a>,
{
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {
        self.as_ref().walk(visitor);
    }
}

impl<'a> WalkVisitor<'a> for Span {
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {}
}

impl<'a> WalkVisitor<'a> for Name {
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {}
}

impl<'a> WalkVisitor<'a> for Identifier {
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {}
}

impl<'a> WalkVisitor<'a> for Lit {
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {}
}

impl<'a> WalkVisitor<'a> for Op {
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {}
}

impl<'a> WalkVisitor<'a> for bool {
    fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {}
}

macro_rules! tuple_impls {
    ($($idx:tt => $args:ident),*) => {
        impl<'a $(, $args: AcceptVisitor<'a>)*> AcceptVisitor<'a> for ($($args),*) {
            fn accept(&'a self, visitor: &mut dyn Visitor<'a>) {
                $(self.$idx.accept(visitor);)*
            }
        }

        impl<'a $(, $args: WalkVisitor<'a>)*> WalkVisitor<'a> for ($($args),*) {
            fn walk(&'a self, visitor: &mut dyn Visitor<'a>) {
                $(self.$idx.walk(visitor);)*
            }
        }

        impl<'a $(, $args: ForEachNode<'a>)*> ForEachNode<'a> for ($($args),*) {
            fn for_each_node(&'a self, each: &mut dyn FnMut(&'a dyn AnyNode<'a>)) {
                $(self.$idx.for_each_node(each);)*
            }
        }
    };
}

tuple_impls!();
tuple_impls!(0 => T0, 1 => T1);
tuple_impls!(0 => T0, 1 => T1, 2 => T2);
tuple_impls!(0 => T0, 1 => T1, 2 => T2, 3 => T3);

pub use self::ExprData::*;
pub use self::StmtKind::*;
pub use self::TypeKindData::*;

// Deprecated names.
pub type ModDecl<'a> = Module<'a>;
pub type IntfDecl<'a> = Interface<'a>;
pub type PackageDecl<'a> = Package<'a>;

/// All things being compiled.
#[moore_derive::node]
#[indefinite("root")]
#[derive(Debug)]
pub struct Root<'a> {
    pub files: Vec<&'a SourceFile<'a>>,
}

/// An entire source file.
#[moore_derive::node]
#[indefinite("source file")]
#[derive(Debug)]
pub struct SourceFile<'a> {
    pub timeunits: Timeunit,
    pub items: Vec<Item<'a>>,
}

/// An item that may appear in a hierarchical scope.
///
/// This includes the following scopes:
/// - file root
/// - modules
/// - interfaces
/// - packages
/// - classes
/// - generates
#[moore_derive::node]
#[indefinite("item")]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Item<'a> {
    #[indefinite("dummy item")]
    Dummy,
    ModuleDecl(#[forward] Module<'a>),
    InterfaceDecl(#[forward] Interface<'a>),
    PackageDecl(#[forward] Package<'a>),
    ClassDecl(#[forward] ClassDecl<'a>),
    ProgramDecl(()),
    ImportDecl(#[forward] ImportDecl<'a>),
    ParamDecl(#[forward] ParamDecl<'a>),
    ModportDecl(ModportDecl),
    Typedef(#[forward] Typedef<'a>),
    PortDecl(#[forward] PortDecl<'a>),
    Procedure(#[forward] Procedure<'a>),
    SubroutineDecl(#[forward] SubroutineDecl<'a>),
    ContAssign(#[forward] ContAssign<'a>),
    GenvarDecl(Vec<GenvarDecl<'a>>),
    GenerateRegion(Span, Vec<Item<'a>>),
    GenerateFor(#[forward] GenerateFor<'a>),
    GenerateIf(#[forward] GenerateIf<'a>),
    GenerateCase(#[forward] GenerateCase<'a>),
    Assertion(Assertion<'a>),
    NetDecl(NetDecl<'a>),
    VarDecl(#[forward] VarDecl<'a>),
    Inst(Inst<'a>),
}

/// A module.
#[moore_derive::node]
#[indefinite("module declaration")]
#[definite("module `{}`", name)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module<'a> {
    pub lifetime: Lifetime, // default static
    #[name]
    pub name: Spanned<Name>,
    pub imports: Vec<ImportDecl<'a>>,
    pub params: Vec<ParamDecl<'a>>,
    pub ports: Vec<Port<'a>>,
    pub items: Vec<Item<'a>>,
}

/// An interface.
#[moore_derive::node]
#[indefinite("interface declaration")]
#[definite("interface `{}`", name)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interface<'a> {
    pub lifetime: Lifetime, // default static
    #[name]
    pub name: Spanned<Name>,
    pub params: Vec<ParamDecl<'a>>,
    pub ports: Vec<Port<'a>>,
    pub items: Vec<Item<'a>>,
}

/// A package.
#[moore_derive::node]
#[indefinite("package declaration")]
#[definite("package `{}`", name)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Package<'a> {
    pub lifetime: Lifetime,
    #[name]
    pub name: Spanned<Name>,
    pub timeunits: Timeunit,
    pub items: Vec<Item<'a>>,
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

/// A type.
#[moore_derive::node]
#[indefinite("type")]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type<'a> {
    pub kind: TypeKind<'a>,
    pub sign: TypeSign,
    pub dims: Vec<TypeDim<'a>>,
}

/// A type without sign and packed dimensions.
#[moore_derive::node]
#[indefinite("type")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind<'a> {
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
    StructType(Struct<'a>),

    // Specialization
    SpecializedType(Box<Type<'a>>, Vec<ParamAssignment<'a>>),

    /// Type reference, such as `type(x)` or `type(int)`.
    TypeRef(Box<TypeOrExpr<'a>>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum TypeSign {
    None,
    Signed,
    Unsigned,
}

#[moore_derive::visit]
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

/// A single entry in an enum.
///
/// For example the `FOO = 42` in `enum { FOO = 42 }`.
#[moore_derive::node]
#[indefinite("enum variant")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumName<'a> {
    #[name]
    pub name: Spanned<Name>,
    pub range: Option<Expr<'a>>,
    pub value: Option<Expr<'a>>,
}

/// A struct definition.
///
/// For example `struct packed { byte foo; }`.
#[moore_derive::node]
#[indefinite("struct definition")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Struct<'a> {
    pub kind: StructKind,
    pub packed: bool,
    pub signing: TypeSign,
    pub members: Vec<StructMember<'a>>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum StructKind {
    Struct,
    Union,
    TaggedUnion,
}

/// A struct field.
///
/// For example the `byte foo;` in `struct packed { byte foo; }`.
#[moore_derive::node]
#[indefinite("struct member")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructMember<'a> {
    pub rand_qualifier: Option<RandomQualifier>,
    pub ty: Box<Type<'a>>,
    pub names: Vec<VarDeclName<'a>>,
}

/// A module or interface port as declared in the port list.
#[moore_derive::node]
#[indefinite("port")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Port<'a> {
    Intf {
        modport: Option<Spanned<Name>>,
        #[name]
        name: Spanned<Name>,
        dims: Vec<TypeDim<'a>>,
        expr: Option<Expr<'a>>,
    },
    Explicit {
        dir: Option<PortDir>,
        #[name]
        name: Spanned<Name>,
        expr: Option<Expr<'a>>,
    },
    Named {
        dir: Option<PortDir>,
        kind: Option<PortKind>,
        ty: Type<'a>,
        #[name]
        name: Spanned<Name>,
        dims: Vec<TypeDim<'a>>,
        expr: Option<Expr<'a>>,
    },
    #[indefinite("implicit port")]
    Implicit(Expr<'a>),
}

impl HasDesc for Port<'_> {
    fn desc(&self) -> &'static str {
        match self.data {
            PortData::Intf { name, .. } => "interface port",
            PortData::Explicit { name, .. } => "explicit port",
            PortData::Named { name, .. } => "port",
            PortData::Implicit(ref expr) => "implicit port",
        }
    }

    fn desc_full(&self) -> String {
        match self.data {
            PortData::Intf { name, .. }
            | PortData::Explicit { name, .. }
            | PortData::Named { name, .. } => format!("{} `{}`", self.desc(), name),
            PortData::Implicit(ref expr) => format!("{} `{}`", self.desc(), expr.span.extract()),
        }
    }
}

/// A port declaration in an item body.
#[moore_derive::node]
#[indefinite("port declaration")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortDecl<'a> {
    pub dir: PortDir,
    pub kind: Option<PortKind>,
    pub ty: Type<'a>,
    pub names: Vec<VarDeclName<'a>>,
}

#[moore_derive::visit]
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

#[moore_derive::visit]
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

#[moore_derive::visit]
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

/// A procedure such as `always*`, `initial`, or `final`.
#[moore_derive::node]
#[indefinite("procedure")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Procedure<'a> {
    pub kind: ProcedureKind,
    pub stmt: Stmt<'a>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum ProcedureKind {
    Initial,
    Always,
    AlwaysComb,
    AlwaysLatch,
    AlwaysFf,
    Final,
}

/// A statement.
#[moore_derive::node]
#[indefinite("statement")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stmt<'a> {
    pub label: Option<Name>,
    pub kind: StmtKind<'a>,
}

/// The different kinds of statement.
#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtKind<'a> {
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
    ImportStmt(ImportDecl<'a>),
    AssertionStmt(Box<Assertion<'a>>),
    WaitExprStmt(Expr<'a>, Box<Stmt<'a>>),
    WaitForkStmt,
    DisableForkStmt,
    DisableStmt(Name),
}

impl<'a> Stmt<'a> {
    pub fn new_null(span: Span) -> Stmt<'a> {
        Stmt::new(
            span,
            StmtData {
                label: None,
                kind: NullStmt,
            },
        )
    }
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum JoinKind {
    All,
    Any,
    None,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum UniquePriority {
    Unique,
    Unique0,
    Priority,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum CaseKind {
    Normal,
    DontCareZ,
    DontCareXZ,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum CaseMode {
    Normal,
    Inside,
    Pattern,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaseItem<'a> {
    Default(Box<Stmt<'a>>),
    Expr(Vec<Expr<'a>>, Box<Stmt<'a>>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DelayControl<'a> {
    pub span: Span,
    pub expr: Expr<'a>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventControl<'a> {
    pub span: Span,
    pub data: EventControlData<'a>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventControlData<'a> {
    Implicit,
    Expr(EventExpr<'a>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CycleDelay {}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimingControl<'a> {
    Delay(DelayControl<'a>),
    Event(EventControl<'a>),
    Cycle(CycleDelay),
}

#[moore_derive::visit]
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

/// A variable declaration.
///
/// For example `logic x, y, z`.
#[moore_derive::node]
#[indefinite("variable declaration")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDecl<'a> {
    pub konst: bool,
    pub var: bool,
    pub lifetime: Option<Lifetime>,
    pub ty: Type<'a>,
    pub names: Vec<VarDeclName<'a>>,
}

/// A variable or net declaration name.
///
/// For example the `x` in `logic x, y, z`.
#[moore_derive::node]
#[indefinite("variable")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDeclName<'a> {
    pub name: Name,
    pub name_span: Span,
    pub dims: Vec<TypeDim<'a>>,
    pub init: Option<Expr<'a>>,
}

/// A generate variable declaration.
#[moore_derive::node]
#[indefinite("genvar")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenvarDecl<'a> {
    #[name]
    pub name: Spanned<Name>,
    pub init: Option<Expr<'a>>,
}

/// An expression.
#[moore_derive::node]
#[indefinite("expression")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr<'a> {
    DummyExpr,
    LiteralExpr(Lit),
    IdentExpr(Identifier),
    SysIdentExpr(Identifier),
    ScopeExpr(Box<Expr<'a>>, Identifier),
    IndexExpr {
        indexee: Box<Expr<'a>>,
        index: Box<Expr<'a>>,
    },
    UnaryExpr {
        op: Op,
        expr: Box<Expr<'a>>,
        postfix: bool,
    },
    BinaryExpr {
        op: Op,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
    TernaryExpr {
        cond: Box<Expr<'a>>,
        true_expr: Box<Expr<'a>>,
        false_expr: Box<Expr<'a>>,
    },
    AssignExpr {
        op: AssignOp,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
    CallExpr(Box<Expr<'a>>, Vec<CallArg<'a>>),
    TypeExpr(Box<Type<'a>>), // TODO: Check if this is still needed, otherwise remove
    ConstructorCallExpr(Vec<CallArg<'a>>),
    ClassNewExpr(Option<Box<Expr<'a>>>),
    ArrayNewExpr(Box<Expr<'a>>, Option<Box<Expr<'a>>>),
    EmptyQueueExpr,
    StreamConcatExpr {
        slice: Option<StreamConcatSlice<'a>>,
        exprs: Vec<StreamExpr<'a>>,
    },
    ConcatExpr {
        repeat: Option<Box<Expr<'a>>>,
        exprs: Vec<Expr<'a>>,
    },
    MinTypMaxExpr {
        min: Box<Expr<'a>>,
        typ: Box<Expr<'a>>,
        max: Box<Expr<'a>>,
    },
    RangeExpr {
        mode: RangeMode,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
    MemberExpr {
        expr: Box<Expr<'a>>,
        name: Identifier,
    },
    PatternExpr(Vec<PatternField<'a>>),
    InsideExpr(Box<Expr<'a>>, Vec<ValueRange<'a>>),
    CastExpr(Type<'a>, Box<Expr<'a>>),
    CastSizeExpr(Box<Expr<'a>>, Box<Expr<'a>>),
    CastSignExpr(Spanned<TypeSign>, Box<Expr<'a>>),
}

#[moore_derive::visit]
#[derive(AnyNodeData, Debug, Clone, PartialEq, Eq)]
#[forward]
pub enum TypeOrExpr<'a> {
    Type(Type<'a>),
    Expr(Expr<'a>),
}

impl<'a> AnyNode<'a> for TypeOrExpr<'a> {
    fn id(&self) -> NodeId {
        match self {
            TypeOrExpr::Type(x) => x.id(),
            TypeOrExpr::Expr(x) => x.id(),
        }
    }

    fn span(&self) -> Span {
        match self {
            TypeOrExpr::Type(x) => x.span(),
            TypeOrExpr::Expr(x) => x.span(),
        }
    }

    fn order(&self) -> usize {
        match self {
            TypeOrExpr::Type(x) => x.order(),
            TypeOrExpr::Expr(x) => x.order(),
        }
    }
}

impl<'a> BasicNode<'a> for TypeOrExpr<'a> {
    fn type_name(&self) -> &'static str {
        match self {
            TypeOrExpr::Type(x) => x.type_name(),
            TypeOrExpr::Expr(x) => x.type_name(),
        }
    }

    fn as_all(&'a self) -> AllNode<'a> {
        match self {
            TypeOrExpr::Type(x) => x.as_all(),
            TypeOrExpr::Expr(x) => x.as_all(),
        }
    }

    fn as_any(&'a self) -> &'a dyn AnyNode<'a> {
        match self {
            TypeOrExpr::Type(x) => x.as_any(),
            TypeOrExpr::Expr(x) => x.as_any(),
        }
    }
}

impl<'a> std::fmt::Display for TypeOrExpr<'a> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TypeOrExpr::Type(x) => std::fmt::Display::fmt(x, fmt),
            TypeOrExpr::Expr(x) => std::fmt::Display::fmt(x, fmt),
        }
    }
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueRange<'a> {
    Single(Expr<'a>),
    Range {
        lo: Expr<'a>,
        hi: Expr<'a>,
        span: Span,
    },
}

#[moore_derive::visit]
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

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallArg<'a> {
    pub span: Span,
    pub name_span: Span,
    pub name: Option<Name>,
    pub expr: Option<Expr<'a>>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StreamConcatSlice<'a> {
    Expr(Box<Expr<'a>>),
    Type(Type<'a>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StreamExpr<'a> {
    pub expr: Box<Expr<'a>>,
    pub range: Option<Box<Expr<'a>>>,
}

#[moore_derive::visit]
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

#[moore_derive::visit]
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

/// A class declaration.
#[moore_derive::node]
#[indefinite("class declaration")]
#[definite("class `{}`", name)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassDecl<'a> {
    pub virt: bool,
    pub lifetime: Lifetime, // default static
    pub name: Spanned<Name>,
    pub params: Vec<ParamDecl<'a>>,
    pub extends: Option<(Type<'a>, Vec<CallArg<'a>>)>,
    pub impls: Vec<Spanned<Name>>,
    pub items: Vec<ClassItem<'a>>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassItem<'a> {
    pub span: Span,
    pub qualifiers: Vec<(ClassItemQualifier, Span)>,
    pub data: ClassItemData<'a>,
}

#[moore_derive::visit]
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

#[moore_derive::visit]
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

#[moore_derive::visit]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RandomQualifier {
    Rand,
    Randc,
}

/// A type definition.
///
/// For example `typedef int my_type_t`.
#[moore_derive::node]
#[indefinite("typedef")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Typedef<'a> {
    #[name]
    pub name: Spanned<Name>,
    pub ty: Type<'a>,
    pub dims: Vec<TypeDim<'a>>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint<'a> {
    pub span: Span,
    pub kind: ConstraintKind,
    pub statik: bool,
    pub name: Name,
    pub name_span: Span,
    pub items: Vec<ConstraintItem<'a>>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    Decl,
    Proto,
    ExternProto,
    PureProto,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintItem<'a> {
    pub span: Span,
    pub data: ConstraintItemData<'a>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintItemData<'a> {
    If,
    Foreach,
    Expr(Expr<'a>),
}

/// A function or task declaration.
#[moore_derive::node]
#[indefinite("subroutine declaration")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutineDecl<'a> {
    pub prototype: SubroutinePrototype<'a>,
    pub items: Vec<SubroutineItem<'a>>,
}

/// A function or task prototype.
#[moore_derive::node]
#[indefinite("subroutine prototype")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePrototype<'a> {
    pub kind: SubroutineKind,
    pub lifetime: Option<Lifetime>,
    #[name]
    pub name: Spanned<Name>,
    pub args: Vec<SubroutinePort<'a>>,
    pub retty: Option<Type<'a>>,
}

#[moore_derive::visit]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SubroutineKind {
    Func,
    Task,
}

/// A function or task port.
#[moore_derive::node]
#[indefinite("subroutine port")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePort<'a> {
    pub dir: Option<SubroutinePortDir>,
    pub var: bool,
    pub ty: Type<'a>,
    pub name: Option<SubroutinePortName<'a>>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePortName<'a> {
    pub name: Spanned<Name>,
    pub dims: Vec<TypeDim<'a>>,
    pub expr: Option<Expr<'a>>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubroutineItem<'a> {
    PortDecl(SubroutinePortDecl<'a>),
    Stmt(Stmt<'a>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubroutinePortDecl<'a> {
    pub span: Span,
    pub dir: SubroutinePortDir,
    pub var: bool,
    pub ty: Type<'a>,
    pub names: Vec<VarDeclName<'a>>,
}

#[moore_derive::visit]
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
    pub net_type: NetType,
    pub strength: Option<NetStrength>,
    pub kind: NetKind,
    pub ty: Type<'a>,
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

#[moore_derive::visit]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetKind {
    Vectored,
    Scalared,
    None,
}

#[moore_derive::visit]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetStrength {
    Drive(DriveStrength, DriveStrength),
    Charge(ChargeStrength),
}

#[moore_derive::visit]
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

#[moore_derive::visit]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChargeStrength {
    Small,
    Medium,
    Large,
}

/// A field in a `'{...}` pattern.
#[moore_derive::node]
#[indefinite("pattern field")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternField<'a> {
    Default(Box<Expr<'a>>),
    Member(Box<Expr<'a>>, Box<Expr<'a>>),
    Type(Type<'a>, Box<Expr<'a>>),
    Expr(Box<Expr<'a>>),
    Repeat(Box<Expr<'a>>, Vec<Expr<'a>>),
}

/// An import declaration.
///
/// For example `import a::b, c::*`.
#[moore_derive::node]
#[indefinite("import declaration")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl<'a> {
    pub items: Vec<ImportItem<'a>>,
}

/// A single import.
///
/// For example the `a::b` in `import a::b, c::*`.
#[moore_derive::node]
#[indefinite("import")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportItem {
    pub pkg: Spanned<Name>,
    pub name: Option<Spanned<Name>>, // None means `import pkg::*`
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assertion<'a> {
    pub span: Span,
    pub label: Option<(Name, Span)>,
    pub data: AssertionData<'a>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionData<'a> {
    Immediate(BlockingAssertion<'a>),
    Deferred(AssertionDeferred, BlockingAssertion<'a>),
    Concurrent(ConcurrentAssertion<'a>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionDeferred {
    /// `assert #0`
    Observed,
    /// `assert final`
    Final,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockingAssertion<'a> {
    Assert(Expr<'a>, AssertionActionBlock<'a>),
    Assume(Expr<'a>, AssertionActionBlock<'a>),
    Cover(Expr<'a>, Stmt<'a>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcurrentAssertion<'a> {
    AssertProperty(PropSpec, AssertionActionBlock<'a>),
    AssumeProperty(PropSpec, AssertionActionBlock<'a>),
    CoverProperty(PropSpec, Stmt<'a>),
    CoverSequence,
    ExpectProperty(PropSpec, AssertionActionBlock<'a>),
    RestrictProperty(PropSpec),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionActionBlock<'a> {
    Positive(Stmt<'a>),
    Negative(Stmt<'a>),
    Both(Stmt<'a>, Stmt<'a>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeqExpr<'a> {
    pub span: Span,
    pub data: SeqExprData<'a>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqExprData<'a> {
    Expr(Expr<'a>, Option<SeqRep<'a>>),
    BinOp(SeqBinOp, Box<SeqExpr<'a>>, Box<SeqExpr<'a>>),
    Throughout(Expr<'a>, Box<SeqExpr<'a>>),
    Clocked(EventExpr<'a>, Box<SeqExpr<'a>>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqRep<'a> {
    Consec(Expr<'a>),    // [* expr]
    ConsecStar,          // [*]
    ConsecPlus,          // [+]
    Nonconsec(Expr<'a>), // [= expr]
    Goto(Expr<'a>),      // [-> expr]
}

#[moore_derive::visit]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeqBinOp {
    Or,
    And,
    Intersect,
    Within,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropSpec;

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropExpr<'a> {
    pub span: Span,
    pub data: PropExprData<'a>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropExprData<'a> {
    SeqOp(PropSeqOp, SeqExpr<'a>),
    SeqBinOp(PropSeqBinOp, PropSeqOp, SeqExpr<'a>, Box<PropExpr<'a>>),
    Not(Box<PropExpr<'a>>),
    BinOp(PropBinOp, Box<PropExpr<'a>>, Box<PropExpr<'a>>),
    Clocked(EventExpr<'a>, Box<PropExpr<'a>>),
}

#[moore_derive::visit]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropSeqOp {
    None,
    Weak,
    Strong,
}

#[moore_derive::visit]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropSeqBinOp {
    ImplOverlap,
    ImplNonoverlap,
    FollowOverlap,
    FollowNonoverlap,
}

#[moore_derive::visit]
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

#[moore_derive::visit]
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

#[moore_derive::visit]
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

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModportDecl {
    pub span: Span,
    pub items: Vec<ModportItem>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModportItem {
    pub span: Span,
    pub name: Identifier,
    pub ports: Vec<ModportPort>,
}

#[moore_derive::visit]
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
#[moore_derive::node]
#[indefinite("parameter")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamDecl<'a> {
    pub local: bool,
    pub kind: ParamKind<'a>,
}

#[moore_derive::visit]
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
#[moore_derive::node]
#[indefinite("type parameter")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamTypeDecl<'a> {
    #[name]
    pub name: Spanned<Name>,
    pub ty: Option<Type<'a>>,
}

/// A single value assignment within a parameter or localparam declaration.
///
/// ```text
/// [type_or_implicit] ident {dimension} ["=" expr]
/// ```
#[moore_derive::node]
#[indefinite("value parameter")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamValueDecl<'a> {
    pub ty: Type<'a>,
    #[name]
    pub name: Spanned<Name>,
    pub dims: Vec<TypeDim<'a>>,
    pub expr: Option<Expr<'a>>,
}

/// A continuous assignment statement.
///
/// ```text
/// "assign" [drive_strength] [delay3] list_of_assignments ";"
/// "assign" [delay_control] list_of_assignments ";"
/// ```
#[moore_derive::node]
#[indefinite("continuous assignment")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContAssign<'a> {
    pub strength: Option<(DriveStrength, DriveStrength)>,
    pub delay: Option<Expr<'a>>,
    pub delay_control: Option<DelayControl<'a>>,
    pub assignments: Vec<(Expr<'a>, Expr<'a>)>,
}

/// A `for` generate statement.
#[moore_derive::node]
#[indefinite("for-generate statement")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateFor<'a> {
    pub init: Stmt<'a>,
    pub cond: Expr<'a>,
    pub step: Expr<'a>,
    pub block: GenerateBlock<'a>,
}

/// An `if` generate statement.
#[moore_derive::node]
#[indefinite("if-generate statement")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateIf<'a> {
    pub cond: Expr<'a>,
    pub main_block: GenerateBlock<'a>,
    pub else_block: Option<GenerateBlock<'a>>,
}

/// A `case` generate statement.
#[moore_derive::node]
#[indefinite("case-generate statement")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateCase {
    // TODO
}

/// A body of a generate construct.
///
/// May contains hierarchy items or more generate constructs.
#[moore_derive::node]
#[indefinite("generate block")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateBlock<'a> {
    pub label: Option<Name>,
    pub items: Vec<Item<'a>>,
}

#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamAssignment<'a> {
    pub span: Span,
    pub name: Option<Identifier>,
    pub expr: TypeOrExpr<'a>,
}

/// A port connection in an instantiation.
///
/// For example:
/// ```verilog
/// foo bar (
///     .*,
///     .name,
///     .name(),
///     .name(expr),
///     expr,
/// );
/// ```
#[moore_derive::node]
#[indefinite("port connection")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PortConn<'a> {
    /// The `.*` case,
    Auto,
    /// The `.name`, `.name()`, or `.name(expr)` cases,
    Named(#[name] Spanned<Name>, PortConnMode<'a>),
    /// The `expr` case,
    Positional(Expr<'a>),
}

/// How a named port connection is made.
#[moore_derive::visit]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PortConnMode<'a> {
    /// The `.name` case.
    Auto,
    /// The `.name()` case.
    Unconnected,
    /// The `.name(expr)` case.
    Connected(Expr<'a>),
}

moore_derive::derive_visitor!();
moore_derive::derive_all_node!();
